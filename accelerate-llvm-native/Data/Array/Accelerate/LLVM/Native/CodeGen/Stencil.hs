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


gangParam2DSides :: ( IR Int, IR Int, IR Int
                    , IR Int, IR Int, IR Int, [LLVM.Parameter])
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
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton Native)
    => (IRArray (Array DIM2 a) -> IR DIM2 -> CodeGen (IR stencil))
    -> Gamma aenv
    -> IRFun1 Native aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest Native aenv (Array DIM2 a)
    -> IRArray (Array DIM2 b)
    -> IR Int
    -> IR Int
    -> CodeGen ()
stencilElement access aenv f boundary (IRManifest v) arrOut x y = do
  let ix = index2D x y
  i     <- intOfIndex (irArrayShape arrOut) ix
  sten  <- access (irArray (aprj v aenv)) ix
  r     <- app1 f sten
  writeArray arrOut i r


middleElement, boundaryElement
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton Native)
    => Gamma aenv
    -> IRFun1 Native aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest Native aenv (Array DIM2 a)
    -> IRArray (Array DIM2 b)
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
mkStencil2D n aenv f boundary ir =
  foldr1 (+++) <$> sequence [ mkStencil2DLeftRight n aenv f boundary ir
                            , mkStencil2DTopBottom n aenv f boundary ir
                            , mkStencil2DMiddle    n aenv f boundary ir
                            ]


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
        middleElement aenv f boundary ir arrOut x y


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
      (start, end, maxBorderOffsetWidth, _, width, _, paramGang) = gangParam2DSides
      (arrOut, paramOut) = mutableArray ("out" :: Name (Array DIM2 b))
      paramEnv           = envParam aenv
  in
  makeOpenAcc "stencil2DLeftRight" (paramGang ++ paramOut ++ paramEnv) $ do
    imapFromTo (int 0) maxBorderOffsetWidth $ \x -> do
      rightx <- sub numType width =<< add numType (int 1) maxBorderOffsetWidth
      imapFromTo start end $ \y -> do
        -- Left
        boundaryElement aenv f boundary ir arrOut x y
        -- Right
        boundaryElement aenv f boundary ir arrOut rightx y



mkStencil2DTopBottom
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton Native)
    => Native
    -> Gamma aenv
    -> IRFun1 Native aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest Native aenv (Array DIM2 a)
    -> CodeGen (IROpenAcc Native aenv (Array DIM2 b))
mkStencil2DTopBottom _ aenv f boundary ir@(IRManifest v) =
  let
      (start, end, _, maxBorderOffsetHeight, _, height, paramGang) = gangParam2DSides
      (arrOut, paramOut) = mutableArray ("out" :: Name (Array DIM2 b))
      paramEnv           = envParam aenv
  in
  makeOpenAcc "stencil2DTopBottom" (paramGang ++ paramOut ++ paramEnv) $ do
    imapFromTo (int 0) maxBorderOffsetHeight $ \y -> do
      bottomy <- sub numType height =<< add numType (int 1) maxBorderOffsetHeight
      imapFromTo start end $ \x -> do
        -- Top
        boundaryElement aenv f boundary ir arrOut x y
        -- Bottom
        boundaryElement aenv f boundary ir arrOut x bottomy
