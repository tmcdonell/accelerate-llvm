{-# LANGUAGE BangPatterns #-}
{-# OPTIONS -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Multi.Array.Data
-- Copyright   : [2014..2015] Trevor L. McDonell
--               [2014..2014] Vinod Grover (NVIDIA Corporation)
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Multi.Array.Data (

  module Data.Array.Accelerate.LLVM.Array.Data,
  unsafeEvict,

) where

-- accelerate
import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.Array.Data
import Data.Array.Accelerate.LLVM.Multi.Target
import Data.Array.Accelerate.LLVM.Multi.Async                   ()
import Data.Array.Accelerate.LLVM.PTX                           ()
import Data.Array.Accelerate.LLVM.PTX.Internal                  ( PTX )
import qualified Data.Array.Accelerate.LLVM.PTX.Internal        as PTX
import qualified Data.Array.Accelerate.Array.Remote.LRU         as LRU

import Data.Array.Accelerate.Array.Sugar                        ( Array )
import qualified Data.Array.Accelerate.Array.Sugar              as Sugar

-- standard
import Data.Proxy
import Control.Monad.Trans                                      ( liftIO )
import Control.Monad.State                                      ( gets )


-- Instance of remote array memory management for the Multi-device target. Since
-- after the execution of every kernel the CPU and GPU memories are
-- synchronised, for the most part no copying is required. The only exception is
-- when we Use an array, in which case we transfer it to all remote targets.
--
instance Remote Multi where

  {-# INLINEABLE allocateRemote #-}
  allocateRemote !sh = do
    arr <- liftIO $! Sugar.allocateArray sh
    n   <- return $! Sugar.size sh
    runArray arr (PTX.mallocArray n) `with` ptxTarget1
    runArray arr (PTX.mallocArray n) `with` ptxTarget2
    return arr

  {-# INLINEABLE useRemoteR #-}
  useRemoteR !n !mst !adata = do
    useRemoteR n (fmap fst mst) adata `with` ptxTarget1
    useRemoteR n (fmap snd mst) adata `with` ptxTarget2


{-# INLINEABLE unsafeEvict #-}
unsafeEvict
    :: Array sh e
    -> LLVM PTX ()
unsafeEvict arr = do
  mt <- gets PTX.ptxMemoryTable
  liftIO $ runArray arr (LRU.unsafeEvict (Proxy :: Proxy (LLVM PTX)) mt)

