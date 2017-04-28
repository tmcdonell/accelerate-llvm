{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE GADTs               #-}
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

import Data.Array.Accelerate.LLVM.Native.Target                     ( Native )
import Data.Array.Accelerate.LLVM.Native.CodeGen.Base
import Data.Array.Accelerate.LLVM.Native.CodeGen.Generate
import Data.Array.Accelerate.LLVM.Native.CodeGen.Loop

import Data.Array.Accelerate.LLVM.CodeGen.Skeleton

import qualified LLVM.AST.Global                                    as LLVM


mkStencil
    :: forall aenv stencil a b sh. (Stencil sh a stencil, Elt b, Skeleton Native)
    => Native
    -> Gamma aenv
    -> IRFun1 Native aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest Native aenv (Array sh a)
    -> CodeGen (IROpenAcc Native aenv (Array sh b))
mkStencil
  | Just Refl <- matchShapeType (undefined :: DIM2) (undefined :: sh)
  = mkStencil2D

  | otherwise
  = defaultStencil1


gangParam2D :: (IR Int, IR Int, IR Int, IR Int, [LLVM.Parameter])
gangParam2D =
  let t      = scalarType
      startx = "ix.start"
      endx   = "ix.end"
      starty = "iy.start"
      endy   = "iy.end"
  in
    ( local t startx
    , local t starty
    , local t endx
    , local t endy
    , [ scalarParameter t startx
      , scalarParameter t starty
      , scalarParameter t endx
      , scalarParameter t endy
      ]
    )


index2D :: IR Int -> IR Int -> IR DIM2
index2D (IR x) (IR y) = IR (OP_Pair (OP_Pair OP_Unit y) x)


stencilElement
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton Native)
    => (IRArray (Array DIM2 a) -> IR DIM2 -> CodeGen (IR stencil))
    -> Gamma aenv
    -> IRFun1 Native aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest Native aenv (Array DIM2 a)
    -> IR Int
    -> IR Int
    -> CodeGen ()
stencilElement access aenv f boundary (IRManifest v) x y =
  let
    arrOut = undefined
  in do
  let ix = index2D x y
  i     <- intOfIndex (irArrayShape arrOut) ix
  sten  <- access (irArray (aprj v aenv)) ix
  r     <- app1 f sten
  writeArray arrOut i r
  return undefined


middleElement, boundaryElement
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton Native)
    => Gamma aenv
    -> IRFun1 Native aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest Native aenv (Array DIM2 a)
    -> IR Int
    -> IR Int
    -> CodeGen ()
middleElement =
  stencilElement (stencilAccess Nothing)
boundaryElement aenv f boundary =
  stencilElement (stencilAccess $ Just boundary) aenv f boundary


mkStencil2D
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton Native)
    => Native
    -> Gamma aenv
    -> IRFun1 Native aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest Native aenv (Array DIM2 a)
    -> CodeGen (IROpenAcc Native aenv (Array DIM2 b))
mkStencil2D _ aenv f boundary (IRManifest v) =
  let
      (x0,y0,x1,y1, paramGang)  = gangParam2D
      x0'                       = add numType x0 borderWidth
      y0'                       = add numType y0 borderHeight
      x1'                       = sub numType x1 borderWidth
      y1'                       = sub numType y1 borderHeight
      (arrOut, paramOut)        = mutableArray ("out" :: Name (Array DIM2 b))
      paramEnv                  = envParam aenv
      --
      stepx = int 1
      stepy = int 1
      undef = $internalError "mkStencil2D" "offsets should not evaluate arguments"
      shapes = offsets (undef :: Fun aenv (stencil -> b))
                       (undef :: OpenAcc aenv (Array DIM2 a))
      (borderWidth, borderHeight) =
        case shapes of
          (Z :. x :. y):_ -> (lift x, lift y)
          _ -> $internalError "mkStencil2D" "2D shape is not 2D"
  in
  makeOpenAcc "stencil2D" (paramGang ++ paramOut ++ paramEnv) $ do

    startx <- x0'
    starty <- y0'
    endx   <- x1'
    endy   <- y1'

    -- Middle section of matrix.
    imapFromStepTo starty stepx endy $ \y -> do
      imapFromStepTo startx stepy endx $ \x -> do
        middleElement aenv f boundary (IRManifest v) x y

    -- Edges section of matrix.

    -- Top and bottom (with corners).
    maxYoffset <- sub numType borderHeight (int 1)

    imapFromTo (int 0) maxYoffset $ \ytop -> do
      imapFromTo x0 x1 $ \x -> do
        ybottom <- sub numType y1 ytop
        boundaryElement aenv f boundary (IRManifest v) x ytop
        boundaryElement aenv f boundary (IRManifest v) x ybottom

    -- Left and right (without corners).
    maxXoffset <- sub numType borderWidth (int 1)
    y0noCorners <- add numType y0 borderWidth
    y1noCorners <- sub numType y1 borderWidth

    imapFromTo y0noCorners y1noCorners $ \y -> do
      imapFromTo (int 0) maxXoffset $ \xleft -> do
        xright <- sub numType x1 xleft
        boundaryElement aenv f boundary (IRManifest v) xleft  y
        boundaryElement aenv f boundary (IRManifest v) xright y

    return_


mkStencil2DMiddle
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton Native)
    => Native
    -> Gamma aenv
    -> IRFun1 Native aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest Native aenv (Array DIM2 a)
    -> CodeGen (IROpenAcc Native aenv (Array DIM2 b))
mkStencil2DMiddle _ aenv f boundary ir@(IRManifest v) =
  let
      (x0,y0,x1,y1, paramGang) = gangParam2D
      (arrOut, paramOut)       = mutableArray ("out" :: Name (Array DIM2 b))
      paramEnv                 = envParam aenv
  in
  makeOpenAcc "stencil2DMiddle" (paramGang ++ paramOut ++ paramEnv) $ do
    imapFromTo y0 y1 $ \y ->
      imapFromTo x0 x1 $ \x ->
        middleElement aenv f boundary ir x y


mkStencil2DLeftRight
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton Native)
    => Native
    -> Gamma aenv
    -> IRFun1 Native aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest Native aenv (Array DIM2 a)
    -> CodeGen (IROpenAcc Native aenv (Array DIM2 b))
mkStencil2DLeftRight _ aenv f boundary ir@(IRManifest v) =
  let
      (start, end, paramGang)   = gangParam
      (arrOut, paramOut)        = mutableArray ("out" :: Name (Array DIM2 b))
      paramEnv                  = envParam aenv
      maxBorderOffsetWidth      = local           scalarType ("ix.maxBorderOffsetWidth" :: Name Int)
      height                    = local           scalarType ("ix.height"               :: Name Int)
      width                     = local           scalarType ("ix.width"                :: Name Int)
      paramMaxBorderOffsetWidth = scalarParameter scalarType ("ix.maxBorderOffsetWidth" :: Name Int)
      paramHeight               = scalarParameter scalarType ("ix.height"               :: Name Int)
      paramWidth                = scalarParameter scalarType ("ix.width"                :: Name Int)
  in
  makeOpenAcc "stencil2DLeftRight" (paramGang ++
                                    paramMaxBorderOffsetWidth :
                                    paramWidth :
                                    paramHeight :
                                    paramOut ++
                                    paramEnv) $ do
    imapFromTo (int 0) maxBorderOffsetWidth $ \x -> do
      rightx <- sub numType width =<< add numType (int 1) maxBorderOffsetWidth
      imapFromTo start end $ \y -> do
        -- Left
        boundaryElement aenv f boundary ir x y
        -- Right
        boundaryElement aenv f boundary ir rightx y



mkStencil2DTopBottom
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton Native)
    => Native
    -> Gamma aenv
    -> IRFun1 Native aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest Native aenv (Array DIM2 a)
    -> CodeGen (IROpenAcc Native aenv (Array DIM2 b))
mkStencil2DTopBottom _ aenv f boundary (IRManifest v) =
  undefined
