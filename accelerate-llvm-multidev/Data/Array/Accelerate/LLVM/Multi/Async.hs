{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Multi.Async
-- Copyright   : [2014..2015] Trevor L. McDonell
--               [2014..2014] Vinod Grover (NVIDIA Corporation)
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Multi.Async (

  Async, Stream, Event,
  module Data.Array.Accelerate.LLVM.Async,

) where

-- accelerate-llvm
import Data.Array.Accelerate.LLVM.Async                         hiding ( Async )
import qualified Data.Array.Accelerate.LLVM.Async               as A

import Data.Array.Accelerate.LLVM.PTX.Internal                  ( PTX(..) )
import qualified Data.Array.Accelerate.LLVM.PTX.Internal        as PTX
import qualified Data.Array.Accelerate.LLVM.PTX.Execute.Stream  as Stream

import Data.Array.Accelerate.LLVM.Multi.Target

-- standard library
import Control.Exception
import Control.Monad.State


type Async a = A.AsyncR Multi a
type Stream  = A.StreamR Multi
type Event   = A.EventR Multi

-- The multi-device backend must ensure that operations proceed asynchronously
-- with respect to both GPU backends (and technically the CPU backend as well,
-- but we know that it just does things synchronously).
--
instance A.Async Multi where
  type StreamR Multi = (PTX.Stream, PTX.Stream)
  type EventR Multi  = (PTX.Event, PTX.Event)

  {-# INLINEABLE block #-}
  block (e1, e2) = do
    A.block e1 `with` ptxTarget1
    A.block e2 `with` ptxTarget2

  {-# INLINEABLE after #-}
  after (s1, s2) (e1, e2) = do
    A.after s1 e1 `with` ptxTarget1
    A.after s2 e2 `with` ptxTarget2

  {-# INLINEABLE waypoint #-}
  waypoint (s1, s2) = do
    e1 <- A.waypoint s1 `with` ptxTarget1
    e2 <- A.waypoint s2 `with` ptxTarget2
    return (e1, e2)

  {-# INLINEABLE async #-}
  async f = do
    ptx1 <- gets ptxTarget1
    ptx2 <- gets ptxTarget2
    s1   <- liftIO $ Stream.create (ptxContext ptx1) (ptxStreamReservoir ptx1) `using` ptx1
    s2   <- liftIO $ Stream.create (ptxContext ptx2) (ptxStreamReservoir ptx2) `using` ptx2
    f (s1,s2)

using :: IO a -> PTX -> IO a
using action ptx =
  bracket_ (PTX.push (ptxContext ptx)) (PTX.pop) action

