{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Multi.Execute.Async
-- Copyright   : [2014..2015] Trevor L. McDonell
--               [2014..2014] Vinod Grover (NVIDIA Corporation)
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Multi.Execute.Async (

  Async, Stream,
  A.wait, A.after, A.streaming, A.async,

) where

-- accelerate-llvm
import Data.Array.Accelerate.LLVM.PTX.Internal                  ( PTX(..) )
import qualified Data.Array.Accelerate.LLVM.PTX.Internal        as PTX
import qualified Data.Array.Accelerate.LLVM.Execute.Async       as A

import qualified Data.Array.Accelerate.LLVM.PTX.Execute.Event   as Event
import qualified Data.Array.Accelerate.LLVM.PTX.Execute.Stream  as Stream

import Data.Array.Accelerate.LLVM.Multi.Target

-- standard library
import Control.Exception
import Control.Monad.State


type Async a = (A.AsyncR PTX a, A.AsyncR PTX a)
type Stream  = (A.StreamR PTX, A.StreamR PTX)

-- The multi-device backend must ensure that operations proceed asynchronously
-- with respect to both GPU backends (and technically the CPU backend as well,
-- but we know that it just does things synchronously).
--
instance A.Async Multi where
  type AsyncR Multi a = Async a
  type StreamR Multi  = Stream

  {-# INLINE wait #-}
  wait (a1, a2) = do
    A.wait a1 `with` ptxTarget1
    A.wait a2 `with` ptxTarget2

  {-# INLINE after #-}
  after (s1, s2) (a1, a2) = do
    A.after s1 a1 `with` ptxTarget1
    A.after s2 a2 `with` ptxTarget2

  {-# INLINE streaming #-}
  streaming f g = do
    ptx1 <- gets ptxTarget1
    ptx2 <- gets ptxTarget2
    st1  <- liftIO $ Stream.create (ptxContext ptx1) (ptxStreamReservoir ptx1) `using` ptx1
    st2  <- liftIO $ Stream.create (ptxContext ptx2) (ptxStreamReservoir ptx2) `using` ptx2
    x    <- f (st1, st2)
    e1   <- liftIO $ Event.waypoint st1 `using` ptx1
    e2   <- liftIO $ Event.waypoint st2 `using` ptx2
    y    <- g (PTX.Async e1 x, PTX.Async e2 x)
    liftIO $ do Stream.destroy (ptxContext ptx1) (ptxStreamReservoir ptx1) st1 `using` ptx1
                Stream.destroy (ptxContext ptx2) (ptxStreamReservoir ptx2) st2 `using` ptx2
                Event.destroy e1 `using` ptx1
                Event.destroy e2 `using` ptx2
    return y

  {-# INLINE async #-}
  async (s1, s2) a = do
    ptx1 <- gets ptxTarget1
    ptx2 <- gets ptxTarget2
    r    <- a
    e1   <- liftIO $ Event.waypoint s1 `using` ptx1
    e2   <- liftIO $ Event.waypoint s2 `using` ptx2
    return (PTX.Async e1 r, PTX.Async e2 r)

using :: IO a -> PTX -> IO a
using action ptx =
  bracket_ (PTX.push (ptxContext ptx)) (PTX.pop) action

