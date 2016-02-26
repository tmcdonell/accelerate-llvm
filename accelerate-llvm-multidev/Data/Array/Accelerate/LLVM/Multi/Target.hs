{-# LANGUAGE CPP             #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Multi.Target
-- Copyright   : [2014..2015] Trevor L. McDonell
--               [2014..2014] Vinod Grover (NVIDIA Corporation)
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Multi.Target
  where

-- accelerate
import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.PTX.Internal                  ( PTX, evalPTX )
import Data.Array.Accelerate.LLVM.Native.Internal               ( Native, evalNative )

import Control.Parallel.Meta.Worker

-- standard library
import Control.Monad.State


-- | The multi-device target is a collection of several manifest targets; in
-- this case the PTX generating GPU backend as well as the native backend for
-- execution on the host CPU. Thus, we can execute a given Accelerate operation
-- with either or both of these target backends.
--
data Multi = Multi {
    ptxTarget1          :: {-# UNPACK #-} !PTX
  , ptxTarget2          :: {-# UNPACK #-} !PTX
  , nativeTarget        :: {-# UNPACK #-} !Native
  , monitorGang         :: {-# UNPACK #-} !Gang
  }


class With backend where
  with :: LLVM backend a -> (Multi -> backend) -> LLVM Multi a

instance With Native where
  {-# INLINEABLE with #-}
  with action f = do
    target <- gets f
    liftIO $ evalNative target action

instance With PTX where
  {-# INLINEABLE with #-}
  with action f = do
    target <- gets f
    liftIO $ evalPTX target action

