{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.Async
-- Copyright   : [2014..2015] Trevor L. McDonell
--               [2014..2014] Vinod Grover (NVIDIA Corporation)
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.Async (

  Async, Stream, Event,
  module Data.Array.Accelerate.LLVM.Async,

) where

-- accelerate
import Data.Array.Accelerate.LLVM.Async                         hiding ( Async )
import qualified Data.Array.Accelerate.LLVM.Async               as A

import Data.Array.Accelerate.LLVM.Native.Target


type Async a = A.AsyncR Native a
type Stream  = A.StreamR Native
type Event   = A.EventR Native

-- The native backend does everything synchronously.
--
instance A.Async Native where
  type EventR Native  = ()
  type StreamR Native = ()

  {-# INLINE block #-}
  block () = return ()

  {-# INLINE after #-}
  after () () = return ()

  {-# INLINE waypoint #-}
  waypoint () = return ()

  {-# INLINE async #-}
  async f = f ()

