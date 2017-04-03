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
import Data.Array.Accelerate.Analysis.Stencil
import Data.Array.Accelerate.Array.Sugar                            ( Array, DIM2, Shape, Elt, Z(..), (:.)(..) )
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
    :: forall aenv stencil a b sh. (Stencil sh a stencil, Elt b)
    => Gamma aenv
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


index1d :: IR Int -> IR Int -> IR Int -> CodeGen (IR Int)
index1d width x y = add numType x =<< mul numType y width  


mkStencil2D
    :: forall aenv stencil a b sh. (Stencil DIM2 a stencil, Elt b)
    => Gamma aenv
    -> IRFun1 Native aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest Native aenv (Array DIM2 a)
    -> CodeGen (IROpenAcc Native aenv (Array DIM2 b))
mkStencil2D aenv apply _ _ =
  let
      (x0,y0,x1,y1, paramGang)  = gangParam2D
      x0'                       = add numType x0 (lift 1) -- Change 1 to stencil size
      y0'                       = add numType y0 (lift 1) -- using offsets function
      x1'                       = sub numType x1 (lift 1)
      y1'                       = sub numType y1 (lift 1)
      (arrOut, paramOut)        = mutableArray ("out" :: Name (Array DIM2 b))
      paramEnv                  = envParam aenv
      --
      stepx = lift (1 :: Int)
      stepy = lift (1 :: Int)
      shapes = offsets (undefined :: Fun aenv (stencil -> b))
                       (undefined :: OpenAcc aenv (Array DIM2 a))
      (borderWidth, borderHeight) =
        case shapes of
          (Z :. x :. y):_ -> (lift x, lift y)
          _ -> error "This should never happen (mkStencil2D)."
  in
  makeOpenAcc "stencil2D" (paramGang ++ paramOut ++ paramEnv) $ do

    startx <- x0'
    starty <- y0'
    endx   <- x1'
    endy   <- y1'

    imapFromStepTo y0 stepx y1 $ \y -> do
      imapFromStepTo x0 stepy x1 $ \x -> do
        i <- index1d x1 x y

        -- stencilAccess

        -- writeArray
        return ()

    return_

