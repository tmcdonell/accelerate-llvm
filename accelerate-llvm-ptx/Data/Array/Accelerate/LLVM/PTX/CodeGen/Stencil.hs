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


gangParam2DSides :: ( IR Int32, IR Int32, IR Int32
                    , IR Int32, IR Int32, IR Int32, [LLVM.Parameter])
gangParam2DSides =
  let t            = scalarType
      start        = "ix.start"
      end          = "ix.end"
      offsetWidth  = "ix.maxBorderOffsetWidth"
      offsetHeight = "ix.maxBorderOffsetHeight"
      width        = "ix.width"
      height       = "ix.height"
  in
    ( local t start
    , local t end
    , local t offsetWidth
    , local t offsetHeight
    , local t width
    , local t height
    , [ scalarParameter t start
      , scalarParameter t end
      , scalarParameter t offsetWidth
      , scalarParameter t offsetHeight
      , scalarParameter t width
      , scalarParameter t height
      ]
    )


index2D :: IR Int -> IR Int -> IR DIM2
index2D (IR x) (IR y) = IR (OP_Pair (OP_Pair OP_Unit y) x)


stencilElement
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton PTX)
    => Maybe (Boundary (IR a))
    -> Gamma aenv
    -> IRFun1 PTX aenv (stencil -> b)
    -> IRManifest PTX aenv (Array DIM2 a)
    -> IRArray (Array DIM2 b)
    -> IR Int32
    -> IR Int32
    -> CodeGen ()
stencilElement mBoundary aenv f (IRManifest v) arrOut x y = do
  x'    <- A.fromIntegral integralType numType x
  y'    <- A.fromIntegral integralType numType y
  let ix = index2D x' y'
  i     <- intOfIndex (irArrayShape arrOut) ix
  sten  <- stencilAccess mBoundary (irArray (aprj v aenv)) ix
  r     <- app1 f sten
  writeArray arrOut i r


middleElement, boundaryElement
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton PTX)
    => Boundary (IR a)
    -> Gamma aenv
    -> IRFun1 PTX aenv (stencil -> b)
    -> IRManifest PTX aenv (Array DIM2 a)
    -> IRArray (Array DIM2 b)
    -> IR Int32
    -> IR Int32
    -> CodeGen ()
middleElement   _        = stencilElement  Nothing
boundaryElement boundary = stencilElement (Just boundary)


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
mkStencil2DMiddle ptx aenv f boundary ir@(IRManifest v) =
  let
      (y0,y1,x0,x1, paramGang) = gangParam2D
      (arrOut, paramOut)       = mutableArray ("out" :: Name (Array DIM2 b))
      paramEnv                 = envParam aenv
  in
  makeOpenAcc ptx "stencil2DMiddle" (paramGang ++ paramOut ++ paramEnv) $ do
    imapFromTo y0 y1 $ \y ->
      imapFromTo x0 x1 $ \x ->
        middleElement boundary aenv f ir arrOut x y

    return_


mkStencil2DLeftRight
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton PTX)
    => PTX
    -> Gamma aenv
    -> IRFun1 PTX aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest PTX aenv (Array DIM2 a)
    -> CodeGen (IROpenAcc PTX aenv (Array DIM2 b))
mkStencil2DLeftRight ptx aenv f boundary ir@(IRManifest v) =
  let
      (start, end, maxBorderOffsetWidth, _, width, _, paramGang) = gangParam2DSides
      (arrOut, paramOut) = mutableArray ("out" :: Name (Array DIM2 b))
      paramEnv           = envParam aenv
  in
  makeOpenAcc ptx "stencil2DLeftRight" (paramGang ++ paramOut ++ paramEnv) $ do
    imapFromTo (int32 0) maxBorderOffsetWidth $ \x -> do
      rightx <- sub numType width =<< add numType (int32 1) x
      imapFromTo start end $ \y -> do
        -- Left
        boundaryElement boundary aenv f ir arrOut x y
        -- Right
        boundaryElement boundary aenv f ir arrOut rightx y

    return_


mkStencil2DTopBottom
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton PTX)
    => PTX
    -> Gamma aenv
    -> IRFun1 PTX aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest PTX aenv (Array DIM2 a)
    -> CodeGen (IROpenAcc PTX aenv (Array DIM2 b))
mkStencil2DTopBottom ptx aenv f boundary ir@(IRManifest v) =
  let
      (start, end, _, maxBorderOffsetHeight, _, height, paramGang) = gangParam2DSides
      (arrOut, paramOut) = mutableArray ("out" :: Name (Array DIM2 b))
      paramEnv           = envParam aenv
  in
  makeOpenAcc ptx "stencil2DTopBottom" (paramGang ++ paramOut ++ paramEnv) $ do
    imapFromTo (int32 0) maxBorderOffsetHeight $ \y -> do
      bottomy <- sub numType height =<< add numType (int32 1) y
      imapFromTo start end $ \x -> do
        -- Top
        boundaryElement boundary aenv f ir arrOut x y
        -- Bottom
        boundaryElement boundary aenv f ir arrOut x bottomy

    return_
