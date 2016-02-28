{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies    #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.Async
-- Copyright   : [2014..2015] Trevor L. McDonell
--               [2014..2014] Vinod Grover (NVIDIA Corporation)
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.Async (

  Async, Stream, Event,
  module Data.Array.Accelerate.LLVM.Async,

) where

-- accelerate
import Data.Array.Accelerate.LLVM.Async                         hiding ( Async )
import qualified Data.Array.Accelerate.LLVM.Async               as A

import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.PTX.Target
import Data.Array.Accelerate.LLVM.PTX.Execute.Event             ( Event )
import Data.Array.Accelerate.LLVM.PTX.Execute.Stream            ( Stream )
import qualified Data.Array.Accelerate.LLVM.PTX.Execute.Event   as Event
import qualified Data.Array.Accelerate.LLVM.PTX.Execute.Stream  as Stream

-- standard library
import Control.Monad.State


type Async a = A.AsyncR PTX a

instance A.Async PTX where
  type StreamR PTX = Stream
  type EventR PTX  = Event

  {-# INLINEABLE block #-}
  block event = liftIO $ Event.block event

  {-# INLINEABLE after #-}
  after stream event = liftIO $ Event.after event stream

  {-# INLINEABLE waypoint #-}
  waypoint stream = liftIO $ Event.waypoint stream

  {-# INLINEABLE async #-}
  async action = do
    PTX{..} <- gets llvmTarget
    stream  <- liftIO $ Stream.create ptxContext ptxStreamReservoir
    action stream

