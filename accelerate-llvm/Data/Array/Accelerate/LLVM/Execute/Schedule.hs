{-# LANGUAGE BangPatterns    #-}
{-# LANGUAGE TemplateHaskell #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Execute.Schedule
-- Copyright   : [2016..2017] Manuel M T Chakravarty, Gabriele Keller, Robert Clifton-Everest, Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Robert Clifton-Everest <robertce@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
module Data.Array.Accelerate.LLVM.Execute.Schedule (

  Schedule(..),
  sequential, parallelChunked,

) where

import Data.Array.Accelerate.Error
import qualified Data.Array.Accelerate.Debug              as Debug

import Data.Time.Clock
import GHC.Conc
import System.IO.Unsafe                                   ( unsafePerformIO )


data Change = Increase | Maintain | Decrease | Unknown
  deriving (Eq, Show)

data Schedule index = Schedule
  { sched_index     :: !index
  , sched_size      :: !Int
  , sched_contains  :: !(Int -> Bool)
  , sched_next      :: !(Float -> IO (Schedule index))
  }

sequential :: Int -> IO (Schedule Int)
sequential i =
  return $ Schedule
    { sched_index     = i
    , sched_size      = 1
    , sched_contains  = \x -> i < x
    , sched_next      = \_ -> sequential (i+1)
    }

parallelChunked :: Int -> Int -> IO (Schedule (Int,Int))
parallelChunked s n
  | Just n' <- fixedChunkSize = mkFixed s n' 0
  | otherwise                 = do
      now <- getCurrentTime
      return $ Schedule
        { sched_index     = (s,n)
        , sched_size      = n
        , sched_contains  = \x -> s < x
        , sched_next      = mkSched now 0 0 0 0 s n Unknown
        }
  where
    mkFixed :: Int -> Int -> Float -> IO (Schedule (Int,Int))
    mkFixed size old_start _ =
      let
          new_start = old_start + size
      in
      return $ Schedule
        { sched_index     = (new_start, size)
        , sched_size      = size
        , sched_contains  = \x -> new_start < x
        , sched_next      = mkFixed size new_start
        }

    -- TLM: This assumes that the scheduler will be called immediately after the
    --      actual computation finishes, but this might not be the case. Should
    --      we pass in a 'NominalDiffTime' instead?
    --
    mkSched :: UTCTime -> Float -> Float -> Float -> Float -> Int -> Int -> Change -> Float -> IO (Schedule (Int,Int))
    mkSched old_time old_load_avg old_load_inst old_time_avg old_time_inst old_start old_size old_decision time = do
      new_time <- getCurrentTime
      let
          alpha       = 0.2
          elapsed     = realToFrac (diffUTCTime new_time old_time)
          load_inst   = time / elapsed
          load_avg    = ema alpha elapsed old_load_avg old_load_inst load_inst
          time_avg    = ema alpha elapsed old_time_avg old_time_inst time
          --
          change      = decision old_decision old_load_avg old_time_avg load_avg time_avg
          new_size
            = (if change /= old_decision
                then trace ("new decision: " ++ show change)
                else id)
            $ apply change old_size
          new_start   = old_start + old_size
      --
      return $ Schedule
        { sched_index     = (new_start, new_size)
        , sched_size      = new_size
        , sched_contains  = \x -> new_start < x
        , sched_next      = mkSched new_time load_avg load_inst time_avg time new_start new_size change
        }

    -- Note: [Sequence chunk size decision strategy]
    --
    -- Determine what the size of the next chunk should be. We have two
    -- competing requirements here: (1) maximise processor utilisation; while
    -- (2) minimising the time spent on each chunk.
    --
    -- Strategy:
    --
    --   1. If the overall processor productivity is below a threshold, always
    --      increase the chunk size. This is particularly important when the
    --      computation is bootstrapping from small chunk sizes, when timings
    --      are inaccurate and we are probably just measuring the time to
    --      schedule and launch the operation.
    --
    --      Note that the minimum productivity we should aim for is really
    --      backend dependent; e.g. based on the number of CPUs.
    --
    --   2. If the processor is sufficiently utilised; i.e. above the minimum
    --      threshold and did not decrease due to the previous change, we might
    --      try decreasing the size of the chunks.
    --
    -- Additionally, note that:
    --
    --   1. We are more aggressive when increasing chunk sizes (*4) compared to
    --      decreasing them (/2). This biases towards keeping the machine loaded
    --      with enough work.
    --
    --   2. When comparing changes, don't assume that doubling the size of each
    --      element should take twice as long. Real workloads rarely scale
    --      linearly like that.
    --
    decision :: Change -> Float -> Float -> Float -> Float -> Change
    decision Unknown _        _        _    _    = Increase
    decision prev    old_load old_time load time =
      let
          resolve EQ = Maintain
          resolve GT = Decrease
          resolve LT = Increase
      in
      if load < targetLoad || cmp old_load load == LT
        then Increase
        else case prev of
               Increase -> resolve (cmp (old_time * 2) time)
               Maintain -> resolve (cmp old_time       time)
               Decrease -> resolve (cmp old_time       (time * 1.5))
               Unknown  -> Increase -- we should never get here

    apply :: Change -> Int -> Int
    apply Increase sz = sz * 4
    apply Maintain sz = sz
    apply Decrease sz = sz `quot` 2
    apply Unknown  sz = apply Increase sz

    -- XXX FIXME: This is really backend dependent, and in particular dependent
    -- on the current execution context; i.e. the CPU backend might be executing
    -- with fewer than the current number of RTS threads, or the PTX backend may
    -- be running with more than one RTS thread even though there is only one
    -- device.
    --
    targetLoad :: Float
    targetLoad = 0.85 * fromIntegral numCapabilities

    -- Approximate ordering. Relative differences less than the epsilon are
    -- consider equal.
    --
    cmp :: Float -> Float -> Ordering
    cmp u v
      | isInfinite u  = timingError
      | isInfinite v  = timingError
      | isNaN u       = timingError
      | isNaN v       = timingError
      | u > v         = if ((u-v) / u) < epsilon then EQ else GT
      | otherwise     = if ((v-u) / v) < epsilon then EQ else LT

    epsilon :: Float
    epsilon = 0.1

    timingError = $internalError "schedule" "unexpected time measurements"


-- Exponential moving average
-- --------------------------

-- Weighted exponential moving average for irregular time series
--
ema :: Float -> Float -> Float -> Float -> Float -> Float
ema !alpha !dt !old_ema !old_sample !new_sample =
  let
      a = dt / alpha
      u = exp ( -a )
      v = ( 1 - u ) / a
  in
  (u * old_ema) + ((v-u) * old_sample) + ((1-v) * new_sample)


-- Debugging
-- =========

{-# INLINE trace #-}
trace :: String -> a -> a
trace msg = Debug.trace Debug.dump_sched ("sched/sequences: " ++ msg)


-- TLM: Is this meant to be a feature? We should have some always-enabled RTS
-- flags if so, rather than requiring debugging mode to be turned on.
--
{-# NOINLINE fixedChunkSize #-}
fixedChunkSize :: Maybe Int
fixedChunkSize = unsafePerformIO $ Debug.queryFlag Debug.seq_chunk_size

