{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.CodeGen.Generate
-- Copyright   : [2013] Trevor L. McDonell, Sean Lee, Vinod Grover
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@nvidia.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.CodeGen.Generate
  where

-- accelerate
import Data.Array.Accelerate.Array.Sugar                        ( Array, Shape, Elt )
import Data.Array.Accelerate.Type

import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.Module
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Type

import Data.Array.Accelerate.LLVM.Native.CodeGen.Base


-- Construct a new array by applying a function to each index. Each thread
-- processes multiple adjacent elements.
--
mkGenerate
    :: forall arch aenv sh e. (Shape sh, Elt e)
    => Gamma aenv
    -> IRFun1 aenv (sh -> e)
    -> CodeGen [Kernel arch aenv (Array sh e)]
mkGenerate aenv apply =
  let
      arrOut                      = arrayData  (undefined::Array sh e) "out"
      shOut                       = arrayShape (undefined::Array sh e) "out"
      paramOut                    = arrayParam (undefined::Array sh e) "out"
      paramEnv                    = envParam aenv
      (start, end, paramGang)     = gangParam
  in
  makeKernel "generate" (paramGang ++ paramOut ++ paramEnv) $ do
    loop        <- newBlock "loop.top"
    exit        <- newBlock "loop.exit"

    -- Entry
    -- -----
    c           <- lt int start end
    top         <- cbr c loop exit

    -- Body
    -- ----
    setBlock loop
    indv        <- freshName                            -- induction variable
    let i       =  local indv
    ix          <- indexOfInt (map local shOut) i       -- convert to multidimensional index
    r           <- apply ix                             -- apply generator function
    writeArray arrOut i r                               -- store result

    i'          <- add int i (constOp $ num int 1)
    c'          <- eq int i' end
    bot         <- cbr c' exit loop
    _           <- phi loop indv (typeOf (int :: IntegralType Int)) [(i',bot), (start,top)]

    setBlock exit
    return_

