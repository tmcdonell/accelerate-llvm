{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.CodeGen.Generate
-- Copyright   : [2014..2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.CodeGen.Generate
  where

import Prelude                                                  hiding ( fromIntegral )

-- accelerate
import Data.Array.Accelerate.Array.Sugar                        ( Array, Shape(..), Elt(..), empty )

import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic
import Data.Array.Accelerate.LLVM.CodeGen.Array
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Sugar

import Data.Array.Accelerate.LLVM.PTX.CodeGen.Base
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Loop
import Data.Array.Accelerate.LLVM.PTX.Target                    ( PTX )


-- Construct a new array by applying a function to each index. Each thread
-- processes multiple adjacent elements.
--
-- This generates two otherwise identical versions which use 32-bit and 64-bit
-- integers for the loop counters. The former is used whenever the output array
-- has all shape components < 32-bits.
--
mkGenerate
    :: (Shape sh, Elt e)
    => PTX
    -> Gamma aenv
    -> IRFun1 PTX aenv (sh -> e)
    -> CodeGen (IROpenAcc PTX aenv (Array sh e))
mkGenerate ptx aenv apply =
  (+++) <$> mkGenerate32 ptx aenv apply
        <*> mkGenerate64 ptx aenv apply

mkGenerate32
    :: forall aenv sh e. (Shape sh, Elt e)
    => PTX
    -> Gamma aenv
    -> IRFun1 PTX aenv (sh -> e)
    -> CodeGen (IROpenAcc PTX aenv (Array sh e))
mkGenerate32 ptx aenv apply =
  let
      (end, paramGang)      = gangParam    (Proxy :: Proxy sh)
      (arrOut, paramOut)    = mutableArray ("out" :: Name (Array sh e))
      paramEnv              = envParam aenv
      shOut                 = irArrayShape arrOut
      start                 = lift (empty :: sh)
  in
  makeOpenAcc ptx "generate32" (paramGang ++ paramOut ++ paramEnv) $ do

    imapNestFromTo32 start end shOut $ \ix i -> do
      r <- app1 apply ix                                -- apply generator function
      writeArray arrOut i r                             -- store result

    return_

mkGenerate64
    :: forall aenv sh e. (Shape sh, Elt e)
    => PTX
    -> Gamma aenv
    -> IRFun1 PTX aenv (sh -> e)
    -> CodeGen (IROpenAcc PTX aenv (Array sh e))
mkGenerate64 ptx aenv apply =
  let
      (end, paramGang)      = gangParam    (Proxy :: Proxy sh)
      (arrOut, paramOut)    = mutableArray ("out" :: Name (Array sh e))
      paramEnv              = envParam aenv
      shOut                 = irArrayShape arrOut
      start                 = lift (empty :: sh)
  in
  makeOpenAcc ptx "generate64" (paramGang ++ paramOut ++ paramEnv) $ do

    imapNestFromTo64 start end shOut $ \ix i -> do
      r <- app1 apply ix                                -- apply generator function
      writeArray arrOut i r                             -- store result

    return_

