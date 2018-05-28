{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.CodeGen.Map
-- Copyright   : [2014..2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.CodeGen.Map
  where

import Prelude                                                  hiding ( fromIntegral )

-- accelerate
import Data.Array.Accelerate.Array.Sugar                        ( Array, Elt, DIM1 )
import Data.Array.Accelerate.Type

import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic            as A
import Data.Array.Accelerate.LLVM.CodeGen.Array
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Sugar

import Data.Array.Accelerate.LLVM.PTX.CodeGen.Base
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Loop
import Data.Array.Accelerate.LLVM.PTX.Target                    ( PTX )


-- Apply a unary function to each element of an array. Each thread processes
-- multiple elements, striding the array by the grid size.
--
mkMap :: forall aenv sh a b. Elt b
      => PTX
      -> Gamma         aenv
      -> IRFun1    PTX aenv (a -> b)
      -> IRDelayed PTX aenv (Array sh a)
      -> CodeGen (IROpenAcc PTX aenv (Array sh b))
mkMap ptx aenv apply array =
  (+++) <$> mkMap32 ptx aenv apply array
        <*> mkMap64 ptx aenv apply array


mkMap32
    :: forall aenv sh a b. Elt b
    => PTX
    -> Gamma         aenv
    -> IRFun1    PTX aenv (a -> b)
    -> IRDelayed PTX aenv (Array sh a)
    -> CodeGen (IROpenAcc PTX aenv (Array sh b))
mkMap32 ptx aenv apply IRDelayed{..} =
  let
      (end, paramGang)      = gangParam    (Proxy :: Proxy DIM1)
      (arrOut, paramOut)    = mutableArray ("out" :: Name (Array sh b))
      paramEnv              = envParam aenv
      start                 = lift 0
  in
  makeOpenAcc ptx "map32" (paramGang ++ paramOut ++ paramEnv) $ do

    end' <- A.fromIntegral integralType numType (indexHead end)

    imapFromTo32 start end' $ \i -> do
      xs <- app1 delayedLinearIndex =<< A.fromIntegral integralType numType i
      ys <- app1 apply xs
      writeArray arrOut i ys

    return_

mkMap64
    :: forall aenv sh a b. Elt b
    => PTX
    -> Gamma         aenv
    -> IRFun1    PTX aenv (a -> b)
    -> IRDelayed PTX aenv (Array sh a)
    -> CodeGen (IROpenAcc PTX aenv (Array sh b))
mkMap64 ptx aenv apply IRDelayed{..} =
  let
      (end, paramGang)      = gangParam    (Proxy :: Proxy DIM1)
      (arrOut, paramOut)    = mutableArray ("out" :: Name (Array sh b))
      paramEnv              = envParam aenv
      start                 = lift 0
  in
  makeOpenAcc ptx "map64" (paramGang ++ paramOut ++ paramEnv) $ do

    imapFromTo64 start (indexHead end) $ \i -> do
      xs <- app1 delayedLinearIndex i
      ys <- app1 apply xs
      writeArray arrOut i ys

    return_

