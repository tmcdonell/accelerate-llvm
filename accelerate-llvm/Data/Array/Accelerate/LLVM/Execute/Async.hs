{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Execute.Async
-- Copyright   : [2014..2016] Trevor L. McDonell
--               [2014..2014] Vinod Grover (NVIDIA Corporation)
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Execute.Async
  where

import Data.Array.Accelerate.LLVM.State
import Control.Applicative
import Prelude


-- Asynchronous operations
-- -----------------------

-- | The result of a potentially parallel computation which will be available at
-- some point (presumably, in the future). This is essentially a write-once
-- IVar.
--
data AsyncR arch a = AsyncR !(Maybe (EventR arch)) !(EventR arch) !a

class Async arch where
  -- | Streams (i.e. threads) can execute concurrently with other streams, but
  -- operations within the same stream proceed sequentially.
  --
  type StreamR arch

  -- | An Event marks a point in the execution stream, possibly in the future.
  -- Since execution within a stream is sequential, events can be used to test
  -- the progress of a computation and synchronise between different streams.
  --
  type EventR arch

  -- | Create a new execution stream that can be used to track (potentially
  -- parallel) computations
  --
  fork        :: LLVM arch (StreamR arch)

  -- | Mark the given execution stream as closed. The stream may still be
  -- executing in the background, but no new work may be submitted to it.
  --
  join        :: StreamR arch -> LLVM arch ()

  -- | Generate a new event at the end of the given execution stream. It will be
  -- filled once all prior work submitted to the stream has completed. The first
  -- argument indicates whether timing information should be recorded.
  --
  -- TLM: I dislike this Bool parameter; maybe we should just always enable
  -- timing information, but we should test what kind of overhead that entails
  -- since for the most part we don't require it. This parameter also makes
  -- 'elapsed' a partial function.
  --
  checkpoint  :: Bool -> StreamR arch -> LLVM arch (EventR arch)

  -- | Make all future work submitted to the given execution stream wait until
  -- the given event has passed. Typically the event is from a different
  -- execution stream, therefore this function is intended to enable
  -- non-blocking cross-stream coordination.
  --
  after       :: StreamR arch -> EventR arch -> LLVM arch ()

  -- | Block execution of the calling thread until the given event has been
  -- recorded.
  --
  block       :: EventR arch -> LLVM arch ()

  -- | Get the processor time (in seconds) which elapsed between the two
  -- completed events. The events must be created with timing enabled.
  --
  elapsed     :: EventR arch -> EventR arch -> LLVM arch Float


-- | Wait for an asynchronous operation to complete, then return it. If timing
-- was enabled for the operation, the elapsed time is returned as well.
--
get :: Async arch
    => AsyncR arch a
    -> LLVM arch (a, Maybe Float)
get (AsyncR me1 e2 a) = do
  block e2
  t <- maybe (return Nothing) (\e1 -> Just <$> elapsed e1 e2) me1
  return (a, t)

-- | Execute the given operation asynchronously in a new execution stream.
--
async :: Async arch
      => Bool                             -- ^ enable timing information?
      -> (StreamR arch -> LLVM arch a)    -- ^ operation to execute asynchronously
      -> LLVM arch (AsyncR arch a)        -- ^ currently executing operation
async timed f = do
  s   <- fork
  e1  <- if timed then Just <$> checkpoint timed s
                  else return Nothing
  r   <- f s
  e2  <- checkpoint timed s
  join s
  return $ AsyncR e1 e2 r

