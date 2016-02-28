{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX
-- Copyright   : [2015] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.Internal (

  PTX(..), Kernel, ptxKernel,
  Async, Event, Stream, streaming,
  executeOp, launch,
  defaultTarget, createTargetForDevice, createTargetFromContext,
  evalPTX,
  mallocArray,

  module Data.Array.Accelerate.LLVM.PTX.Context,

) where

import Data.Array.Accelerate.LLVM.PTX.Compile
import Data.Array.Accelerate.LLVM.PTX.Context
import Data.Array.Accelerate.LLVM.PTX.Execute
import Data.Array.Accelerate.LLVM.PTX.Async
import Data.Array.Accelerate.LLVM.PTX.State
import Data.Array.Accelerate.LLVM.PTX.Target
import Data.Array.Accelerate.LLVM.PTX.Array.Prim                ( mallocArray )

