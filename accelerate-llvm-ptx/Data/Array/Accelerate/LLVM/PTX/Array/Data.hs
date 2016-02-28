{-# LANGUAGE BangPatterns    #-}
{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.Array.Data
-- Copyright   : [2014..2015] Trevor L. McDonell
--               [2014..2014] Vinod Grover (NVIDIA Corporation)
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.Array.Data (

  module Data.Array.Accelerate.LLVM.Array.Data,

) where

-- accelerate
import qualified Data.Array.Accelerate.Array.Sugar              as Sugar

import Data.Array.Accelerate.LLVM.Array.Data
import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.PTX.Target
import Data.Array.Accelerate.LLVM.PTX.Async                     ()
import qualified Data.Array.Accelerate.LLVM.PTX.Array.Prim      as Prim

-- standard library
import Control.Monad.State


-- Instance of remote array memory management for the PTX target
--
instance Remote PTX where

  {-# INLINEABLE allocateRemote #-}
  allocateRemote !sh = do
    arr <- liftIO $! Sugar.allocateArray sh
    n   <- return $! Sugar.size sh
    runArray arr (Prim.mallocArray n)
    return arr

  {-# INLINEABLE useRemoteR #-}
  useRemoteR !n !mst !adata =
    case mst of
      Nothing -> Prim.useArray         n adata
      Just st -> Prim.useArrayAsync st n adata

  {-# INLINEABLE copyToRemoteR #-}
  copyToRemoteR !from !to !mst !adata = do
    case mst of
      Nothing -> Prim.pokeArrayR         from to adata
      Just st -> Prim.pokeArrayAsyncR st from to adata

  {-# INLINEABLE copyToHostR #-}
  copyToHostR !from !to !mst !adata = do
    case mst of
      Nothing -> Prim.peekArrayR         from to adata
      Just st -> Prim.peekArrayAsyncR st from to adata

  {-# INLINEABLE copyToPeerR #-}
  copyToPeerR !from !to !dst !mst !adata = do
    src <- gets llvmTarget
    unless (ptxContext src == ptxContext dst) $
      case mst of
        Nothing -> Prim.copyArrayPeerR      (ptxContext dst) (ptxMemoryTable dst)    from to adata
        Just st -> Prim.copyArrayPeerAsyncR (ptxContext dst) (ptxMemoryTable dst) st from to adata

  {-# INLINEABLE indexRemote #-}
  indexRemote arr i =
    runIndexArray Prim.indexArray arr i

