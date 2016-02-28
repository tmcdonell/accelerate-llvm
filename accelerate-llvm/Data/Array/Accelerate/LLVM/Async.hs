{-# LANGUAGE TypeFamilies #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Async
-- Copyright   : [2014..2016] Trevor L. McDonell
--               [2014..2014] Vinod Grover (NVIDIA Corporation)
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Async
  where

import Data.Array.Accelerate.LLVM.State


-- Asynchronous operations
-- -----------------------

data AsyncR arch a = AsyncR !(EventR arch) !a

class Async arch where
  -- | Streams (i.e. threads) can execute concurrently with other streams, but
  -- operations within the same stream proceed sequentially.
  type StreamR arch

  -- | Events mark a point in the execution stream, possibly in the future. The
  -- can be used to synchronise across streams.
  type EventR arch

  -- | Block until the given event is recorded
  --
  block     :: EventR arch -> LLVM arch ()

  -- | Make all future work submitted to the given execution stream wait until
  -- the given event has completed. This allows cross-stream coordination.
  --
  after     :: StreamR arch -> EventR arch -> LLVM arch ()

  -- | Create a new event marker that will be filled once execution in the
  -- specified stream completes all previously submitted work.
  --
  waypoint  :: StreamR arch -> LLVM arch (EventR arch)

  -- | Execute the given operation asynchronously in a new execution stream.
  --
  async     :: (StreamR arch -> LLVM arch a) -> LLVM arch a


-- | Wait for an asynchronous operation to complete
--
wait :: Async arch => AsyncR arch a -> LLVM arch a
wait (AsyncR e a) = block e >> return a

-- | Execute an operation in a new stream, and make that result available
-- asynchronously in a consumer operation.
--
streaming
    :: Async arch
    => (StreamR arch  -> LLVM arch a)
    -> (AsyncR arch a -> LLVM arch b)
    -> LLVM arch b
streaming this that = do
  a <- async $ \s -> do r <- this s
                        e <- waypoint s
                        return $! AsyncR e r
  that a

