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
import System.CPUTime


type Async a = A.AsyncR  Native a
type Stream  = A.StreamR Native
type Event   = A.EventR  Native

-- The native backend does everything synchronously.
--
instance A.Async Native where
  type StreamR Native = ()
  type EventR  Native = Maybe Integer -- CPU time in picoseconds

  {-# INLINE fork #-}
  fork = return ()

  {-# INLINE join #-}
  join () = return ()

  -- TLM: This is really measuring the time from when the operation was added to
  -- the scheduling DAG, not the time from which execution commenced. This will
  -- be problematic once scheduling is relaxed from the current bulk-synchronous
  -- method.
  --
  {-# INLINEABLE checkpoint #-}
  checkpoint False () = return Nothing
  checkpoint True  () = Just <$> liftIO getCPUTime

  {-# INLINE after #-}
  after () _ = return ()

  {-# INLINE block #-}
  block _ = return ()

  -- TLM: The elapsed time here is the total CPU time, not just the time
  -- actually spent executing. It might be worthwhile doing something akin to
  -- the monitoring infrastructure to get the more accurate result.
  --
  {-# INLINEABLE elapsed #-}
  elapsed (Just cpu0) (Just cpu1) = return $ fromIntegral (cpu1 - cpu0) * 1E-12
  elapsed _           _           = $internalError "elapsed" "timing not enabled for selected events"

