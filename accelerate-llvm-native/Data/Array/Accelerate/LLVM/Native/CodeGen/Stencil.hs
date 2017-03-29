{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.CodeGen.Stencil
-- Copyright   : [2014..2015] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.CodeGen.Stencil
  where

-- accelerate
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Array.Sugar                            ( Array, DIM2 )
import Data.Array.Accelerate.Type

import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic
import Data.Array.Accelerate.LLVM.CodeGen.Array
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Environment
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Loop
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Stencil -- stencilAccess
import Data.Array.Accelerate.LLVM.CodeGen.Sugar

import Data.Array.Accelerate.LLVM.Native.Target                     ( Native )
import Data.Array.Accelerate.LLVM.Native.CodeGen.Base
import Data.Array.Accelerate.LLVM.Native.CodeGen.Generate
import Data.Array.Accelerate.LLVM.Native.CodeGen.Loop

import qualified LLVM.AST.Global                                    as LLVM



mkStencil
    :: forall aenv stencil a b.
       Gamma aenv
    -> IRFun1 Native aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest Native aenv (Array sh a)
    -> CodeGen (IROpenAcc Native aenv (Array sh b))
mkStencil _ _ _ _
  -- | Just Refl <- matchShapeType ...
  -- = mkStencil2D undefined undefined undefined

  | otherwise
  = undefined


gangParam2D :: (IR Int, IR Int, IR Int, IR Int, [LLVM.Parameter])
gangParam2D = undefined

mkStencil2D
    :: forall aenv stencil e. (Stencil DIM2 e stencil)
    => Gamma aenv
    -> IRFun1 Native aenv (stencil -> e)
    -> CodeGen (IROpenAcc Native aenv (Array DIM2 e))
mkStencil2D aenv apply =
  let
      (x0,y0,x1,y1, paramGang)  = gangParam2D
      (arrOut, paramOut)        = mutableArray ("out" :: Name (Array DIM2 e))
      paramEnv                  = envParam aenv
      --
      stepx = undefined
      stepy = undefined
  in
  makeOpenAcc "stencil2D" (paramGang ++ paramOut ++ paramEnv) $ do

    imapFromStepTo y0 (lift 2) y1 $ \y -> do
      imapFromStepTo x0 (lift 2) x1 $ \x -> do

        -- stencilAccess

        -- writeArray
        return ()

    return_

