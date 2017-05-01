{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.Execute.Async
-- Copyright   : [2014..2016] Trevor L. McDonell
--               [2014..2014] Vinod Grover (NVIDIA Corporation)
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.Execute.Async (

  Async, Stream, Event,
  module Data.Array.Accelerate.LLVM.Execute.Async,

) where

-- accelerate
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.LLVM.Execute.Async                     hiding ( Async )
import qualified Data.Array.Accelerate.LLVM.Execute.Async           as A

import Data.Array.Accelerate.LLVM.Native.Target

import Control.Monad.Trans
import Data.Time.Clock
import System.CPUTime


type Async a = A.AsyncR  Native a
type Stream  = A.StreamR Native
type Event   = A.EventR  Native

-- The native backend does everything synchronously.
--
instance A.Async Native where
  type StreamR Native = ()
  type EventR  Native = Maybe (UTCTime, Integer)  -- walltime, cputime
  type TimeR   Native = (Float, Float)            -- walltime, cputime (s)

  {-# INLINE fork #-}
  fork = return ()

  {-# INLINE join #-}
  join () = return ()

  {-# INLINEABLE checkpoint #-}
  checkpoint False () = return Nothing
  checkpoint True  () = liftIO $ do
    wall <- getCurrentTime
    cpu  <- getCPUTime
    return (Just (wall,cpu))

  {-# INLINE after #-}
  after () _ = return ()

  {-# INLINE block #-}
  block _ = return ()

  {-# INLINEABLE elapsed #-}
  elapsed (Just (wall0, cpu0)) (Just (wall1, cpu1)) =
    let wallTime = realToFrac (diffUTCTime wall1 wall0)
        cpuTime  = fromIntegral (cpu1 - cpu0) * 1E-12
    in return (wallTime, cpuTime)
  elapsed _ _ =
    $internalError "elapsed" "timing not enabled for selected events"

