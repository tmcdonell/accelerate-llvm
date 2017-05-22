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
import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic                as A
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

import LLVM.AST.Type.Name
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


int32 :: Int -> IR Int32
int32 = lift . Prelude.fromIntegral


gangParam2D :: (IR Int32, IR Int32, IR Int32, IR Int32, [LLVM.Parameter])
gangParam2D =
  let t      = scalarType
      startx = "ix.start"
      endx   = "ix.end"
      starty = "iy.start"
      endy   = "iy.end"
  in
    ( local t starty
    , local t endy
    , local t startx
    , local t endx
    , [ scalarParameter t starty
      , scalarParameter t endy
      , scalarParameter t startx
      , scalarParameter t endx
      ]
    )


index2D :: IR Int -> IR Int -> IR DIM2
index2D (IR x) (IR y) = IR (OP_Pair (OP_Pair OP_Unit y) x)


index2DToPair :: IR DIM2 -> (IR Int, IR Int)
index2DToPair (IR (OP_Pair (OP_Pair OP_Unit y) x)) = (IR x, IR y)


stencilElement
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton PTX)
    => Maybe (Boundary (IR a))
    -> Gamma aenv
    -> IRFun1 PTX aenv (stencil -> b)
    -> IRManifest PTX aenv (Array DIM2 a)
    -> IRArray (Array DIM2 b)
    -> IR Int
    -> IR Int
    -> CodeGen ()
stencilElement mBoundary aenv f (IRManifest v) arrOut x y = do
  let ix = index2D x y
  i     <- intOfIndex (irArrayShape arrOut) ix
  sten  <- stencilAccess mBoundary (irArray (aprj v aenv)) ix
  r     <- app1 f sten
  writeArray arrOut i r


mkStencil2D
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton PTX)
    => PTX
    -> Gamma aenv
    -> IRFun1 PTX aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest PTX aenv (Array DIM2 a)
    -> CodeGen (IROpenAcc PTX aenv (Array DIM2 b))
mkStencil2D ptx aenv f boundary ir =
  let
      (y0,y1,x0,x1, paramGang) = gangParam2D
  in foldr1 (+++) <$> sequence
       [ runRegion "stencil2DMiddle" (y0, x0) (y1, x1) paramGang ptx aenv f  Nothing        ir
       , runRegion "stencil2DEdge"   (y0, x0) (y1, x1) paramGang ptx aenv f (Just boundary) ir
       , runRegion "stencil2DEnd"    (x0, y0) (x1, y1) paramGang ptx aenv f (Just boundary) ir
       ]


runRegion
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton PTX)
    => Label
    -> (IR Int32, IR Int32)
    -> (IR Int32, IR Int32)
    -> [LLVM.Parameter]
    -> PTX
    -> Gamma aenv
    -> IRFun1 PTX aenv (stencil -> b)
    -> Maybe (Boundary (IR a))
    -> IRManifest PTX aenv (Array DIM2 a)
    -> CodeGen (IROpenAcc PTX aenv (Array DIM2 b))
runRegion label (y0, x0) (y1, x1) paramGang ptx aenv f mBoundary ir =
  let
      (arrOut, paramOut)       = mutableArray ("out" :: Name (Array DIM2 b))
      paramEnv                 = envParam aenv
  in makeOpenAcc ptx label (paramGang ++ paramOut ++ paramEnv) $ do
    localWidth  <- sub numType x1 x0
    localHeight <- sub numType y1 y0
    endi        <- mul numType localWidth localHeight

    x0' <- A.fromIntegral integralType numType x0
    y0' <- A.fromIntegral integralType numType y0

    imapFromTo (int32 0) (endi) $ \i -> do
      localWidth'  <- A.fromIntegral integralType numType localWidth
      localHeight' <- A.fromIntegral integralType numType localHeight
      i'           <- A.fromIntegral integralType numType i -- loop counter is Int32
      (x, y)       <- index2DToPair <$> indexOfInt (index2D localWidth' localHeight') i'
      x'           <- add numType x x0'
      y'           <- add numType y y0'
      stencilElement mBoundary aenv f ir arrOut x' y'

    return_
