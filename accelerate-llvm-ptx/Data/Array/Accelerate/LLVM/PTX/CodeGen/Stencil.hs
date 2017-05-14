{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE GADTs               #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.CodeGen.Stencil
-- Copyright   : [2014..2015] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.CodeGen.Stencil
  where

-- accelerate
import Data.Array.Accelerate.AST                                    hiding (stencilAccess)
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Analysis.Stencil
import Data.Array.Accelerate.Array.Sugar                            ( Array, DIM2, Shape, Elt, Z(..), (:.)(..) )
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Error

import Data.Array.Accelerate.LLVM.Analysis.Match
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

import Data.Array.Accelerate.LLVM.PTX.Target                        ( PTX )
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Base
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Generate
import Data.Array.Accelerate.LLVM.PTX.CodeGen.Loop

import Data.Array.Accelerate.LLVM.CodeGen.Skeleton

import qualified LLVM.AST.Global                                    as LLVM


mkStencil
    :: forall aenv stencil a b sh. (Stencil sh a stencil, Elt b, Skeleton PTX)
    => PTX
    -> Gamma aenv
    -> IRFun1 PTX aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest PTX aenv (Array sh a)
    -> CodeGen (IROpenAcc PTX aenv (Array sh b))
mkStencil
  | Just Refl <- matchShapeType (undefined :: DIM2) (undefined :: sh)
  = mkStencil2D

  | otherwise
  = defaultStencil1


mkStencil2D
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton PTX)
    => PTX
    -> Gamma aenv
    -> IRFun1 PTX aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest PTX aenv (Array DIM2 a)
    -> CodeGen (IROpenAcc PTX aenv (Array DIM2 b))
mkStencil2D n aenv f boundary ir =
  foldr1 (+++) <$> sequence [ mkStencil2DLeftRight n aenv f boundary ir
                            , mkStencil2DTopBottom n aenv f boundary ir
                            , mkStencil2DMiddle    n aenv f boundary ir
                            ]

mkStencil2DMiddle
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton PTX)
    => PTX
    -> Gamma aenv
    -> IRFun1 PTX aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest PTX aenv (Array DIM2 a)
    -> CodeGen (IROpenAcc PTX aenv (Array DIM2 b))
mkStencil2DMiddle _ aenv f boundary ir@(IRManifest v) =
  undefined


mkStencil2DLeftRight
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton PTX)
    => PTX
    -> Gamma aenv
    -> IRFun1 PTX aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest PTX aenv (Array DIM2 a)
    -> CodeGen (IROpenAcc PTX aenv (Array DIM2 b))
mkStencil2DLeftRight _ aenv f boundary ir@(IRManifest v) =
  undefined


mkStencil2DTopBottom
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton PTX)
    => PTX
    -> Gamma aenv
    -> IRFun1 PTX aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest PTX aenv (Array DIM2 a)
    -> CodeGen (IROpenAcc PTX aenv (Array DIM2 b))
mkStencil2DTopBottom _ aenv f boundary ir@(IRManifest v) =
  undefined
