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
import Data.Array.Accelerate.Array.Sugar                            ( Array, DIM2, Elt )
import Data.Array.Accelerate.Type

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

import Data.Array.Accelerate.LLVM.Native.Target                     ( Native )
import Data.Array.Accelerate.LLVM.Native.CodeGen.Base
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


mkStencil2
    :: forall aenv stencil1 stencil2 a b c sh.
       (Stencil sh a stencil1, Stencil sh b stencil2, Elt c, Skeleton Native)
    => Native
    -> Gamma aenv
    -> IRFun2 Native aenv (stencil1 -> stencil2 -> c)
    -> Boundary (IR a)
    -> IRManifest Native aenv (Array sh a)
    -> Boundary (IR b)
    -> IRManifest Native aenv (Array sh b)
    -> CodeGen (IROpenAcc Native aenv (Array sh c))
mkStencil2
  | Just Refl <- matchShapeType (undefined :: DIM2) (undefined :: sh)
  = mkStencil22D

  | otherwise
  = defaultStencil2



gangParam2D :: (IR Int, IR Int, IR Int, IR Int, [LLVM.Parameter])
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


gangParam2DSides :: ( IR Int, IR Int, IR Int
                    , IR Int, IR Int, IR Int, [LLVM.Parameter])
gangParam2DSides =
  let t            = scalarType
      start        = "ix.start"
      end          = "ix.end"
      borderWidth  = "ix.borderWidth"
      borderHeight = "ix.borderHeight"
      width        = "ix.width"
      height       = "ix.height"
  in
    ( local t start
    , local t end
    , local t borderWidth
    , local t borderHeight
    , local t width
    , local t height
    , [ scalarParameter t start
      , scalarParameter t end
      , scalarParameter t borderWidth
      , scalarParameter t borderHeight
      , scalarParameter t width
      , scalarParameter t height
      ]
    )


index2D :: IR Int -> IR Int -> IR DIM2
index2D (IR x) (IR y) = IR (OP_Pair (OP_Pair OP_Unit y) x)


stencilElement
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton Native)
    => Maybe (Boundary (IR a))
    -> Gamma aenv
    -> IRFun1 Native aenv (stencil -> b)
    -> IRManifest Native aenv (Array DIM2 a)
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


stencilElement2
    :: forall aenv stencil1 stencil2 a b c.
       (Stencil DIM2 a stencil1, Stencil DIM2 b stencil2, Elt c, Skeleton Native)
    => Maybe (Boundary (IR a))
    -> Maybe (Boundary (IR b))
    -> Gamma aenv
    -> IRFun2 Native aenv (stencil1 -> stencil2 -> c)
    -> IRManifest Native aenv (Array DIM2 a)
    -> IRManifest Native aenv (Array DIM2 b)
    -> IRArray (Array DIM2 c)
    -> IR Int
    -> IR Int
    -> CodeGen ()
stencilElement2 mB1 mB2 aenv f (IRManifest v1) (IRManifest v2) arrOut x y = do
  let ix = index2D x y
  i     <- intOfIndex (irArrayShape arrOut) ix
  sten1 <- stencilAccess mB1 (irArray (aprj v1 aenv)) ix
  sten2 <- stencilAccess mB2 (irArray (aprj v2 aenv)) ix
  r     <- app2 f sten1 sten2
  writeArray arrOut i r


middleElement, boundaryElement
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton Native)
    => Boundary (IR a)
    -> Gamma aenv
    -> IRFun1 Native aenv (stencil -> b)
    -> IRManifest Native aenv (Array DIM2 a)
    -> IRArray (Array DIM2 b)
    -> IR Int
    -> IR Int
    -> CodeGen ()
middleElement   _        = stencilElement  Nothing
boundaryElement boundary = stencilElement (Just boundary)


middleElement2, boundaryElement2
    :: forall aenv stencil1 stencil2 a b c.
       (Stencil DIM2 a stencil1, Stencil DIM2 b stencil2, Elt c, Skeleton Native)
    => Boundary (IR a)
    -> Boundary (IR b)
    -> Gamma aenv
    -> IRFun2 Native aenv (stencil1 -> stencil2 -> c)
    -> IRManifest Native aenv (Array DIM2 a)
    -> IRManifest Native aenv (Array DIM2 b)
    -> IRArray (Array DIM2 c)
    -> IR Int
    -> IR Int
    -> CodeGen ()
middleElement2   _  _  = stencilElement2  Nothing   Nothing
boundaryElement2 b1 b2 = stencilElement2 (Just b1) (Just b2)


mkStencil2D
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton Native)
    => Native
    -> Gamma aenv
    -> IRFun1 Native aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest Native aenv (Array DIM2 a)
    -> CodeGen (IROpenAcc Native aenv (Array DIM2 b))
mkStencil2D n aenv f boundary ir1 =
  foldr1 (+++) <$> sequence [ mkStencil2DLeftRight n aenv f boundary ir1
                            , mkStencil2DTopBottom n aenv f boundary ir1
                            , mkStencil2DMiddle    n aenv f boundary ir1
                            ]


mkStencil22D
    :: forall aenv stencil1 stencil2 a b c.
       (Stencil DIM2 a stencil1, Stencil DIM2 b stencil2, Elt c, Skeleton Native)
    => Native
    -> Gamma aenv
    -> IRFun2 Native aenv (stencil1 -> stencil2 -> c)
    -> Boundary (IR a)
    -> IRManifest Native aenv (Array DIM2 a)
    -> Boundary (IR b)
    -> IRManifest Native aenv (Array DIM2 b)
    -> CodeGen (IROpenAcc Native aenv (Array DIM2 c))
mkStencil22D n aenv f b1 ir1 b2 ir2 =
  foldr1 (+++) <$> sequence [ mkStencil22DLeftRight n aenv f b1 ir1 b2 ir2
                            , mkStencil22DTopBottom n aenv f b1 ir1 b2 ir2
                            , mkStencil22DMiddle    n aenv f b1 ir1 b2 ir2
                            ]


mkStencil2DMiddle
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton Native)
    => Native
    -> Gamma aenv
    -> IRFun1 Native aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest Native aenv (Array DIM2 a)
    -> CodeGen (IROpenAcc Native aenv (Array DIM2 b))
mkStencil2DMiddle _ aenv f boundary ir1@(IRManifest v) =
  let
      (y0,y1,x0,x1, paramGang) = gangParam2D
      (arrOut, paramOut)       = mutableArray ("out" :: Name (Array DIM2 b))
      paramEnv                 = envParam aenv
  in
  makeOpenAcc "stencil2DMiddle" (paramGang ++ paramOut ++ paramEnv) $ do
    yrange    <- sub numType y1 y0
    remainder <- A.rem integralType yrange (int 4)
    y'        <- sub numType y1 remainder
    --
    imapFromStepTo y0 (int 4) y' $ \y -> do
      y_1 <- add numType y (int 1)
      y_2 <- add numType y (int 2)
      y_3 <- add numType y (int 3)
      imapFromTo x0 x1 $ \x -> do
        let ix = index2D x y
        i0 <- intOfIndex (irArrayShape arrOut) ix
        i1 <- intOfIndex (irArrayShape arrOut) (index2D x y_1)
        i2 <- intOfIndex (irArrayShape arrOut) (index2D x y_2)
        i3 <- intOfIndex (irArrayShape arrOut) (index2D x y_3)
        (s0, s1, s2, s3) <- stencilAccesses Nothing (irArray (aprj v aenv)) ix
        r0 <- app1 f s0
        r1 <- app1 f s1
        r2 <- app1 f s2
        r3 <- app1 f s3
        writeArray arrOut i0 r0
        writeArray arrOut i1 r1
        writeArray arrOut i2 r2
        writeArray arrOut i3 r3
    -- Do the last few rows that aren't in the groups of 4.
    imapFromTo y' y1 $ \y ->
      imapFromTo x0 x1 $ \x ->
        middleElement boundary aenv f ir1 arrOut x y

    return_


mkStencil2DLeftRight
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton Native)
    => Native
    -> Gamma aenv
    -> IRFun1 Native aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest Native aenv (Array DIM2 a)
    -> CodeGen (IROpenAcc Native aenv (Array DIM2 b))
mkStencil2DLeftRight _ aenv f boundary ir1 =
  let
      (start, end, borderWidth, _borderHeight, width, _height, paramGang) = gangParam2DSides
      (arrOut, paramOut) = mutableArray ("out" :: Name (Array DIM2 b))
      paramEnv           = envParam aenv
  in
  makeOpenAcc "stencil2DLeftRight" (paramGang ++ paramOut ++ paramEnv) $ do
    imapFromTo (int 0) borderWidth $ \x -> do
      rightx <- sub numType width =<< add numType (int 1) x
      imapFromTo start end $ \y -> do
        -- Left
        boundaryElement boundary aenv f ir1 arrOut x y
        -- Right
        boundaryElement boundary aenv f ir1 arrOut rightx y

    return_



mkStencil2DTopBottom
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b, Skeleton Native)
    => Native
    -> Gamma aenv
    -> IRFun1 Native aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest Native aenv (Array DIM2 a)
    -> CodeGen (IROpenAcc Native aenv (Array DIM2 b))
mkStencil2DTopBottom _ aenv f boundary ir1 =
  let
      (start, end, _borderWidth, borderHeight, _width, height, paramGang) = gangParam2DSides
      (arrOut, paramOut) = mutableArray ("out" :: Name (Array DIM2 b))
      paramEnv           = envParam aenv
  in
  makeOpenAcc "stencil2DTopBottom" (paramGang ++ paramOut ++ paramEnv) $ do
    imapFromTo (int 0) borderHeight $ \y -> do
      bottomy <- sub numType height =<< add numType (int 1) y
      imapFromTo start end $ \x -> do
        -- Top
        boundaryElement boundary aenv f ir1 arrOut x y
        -- Bottom
        boundaryElement boundary aenv f ir1 arrOut x bottomy

    return_



mkStencil22DMiddle
    :: forall aenv stencil1 stencil2 a b c.
       (Stencil DIM2 a stencil1, Stencil DIM2 b stencil2, Elt c, Skeleton Native)
    => Native
    -> Gamma aenv
    -> IRFun2 Native aenv (stencil1 -> stencil2 -> c)
    -> Boundary (IR a)
    -> IRManifest Native aenv (Array DIM2 a)
    -> Boundary (IR b)
    -> IRManifest Native aenv (Array DIM2 b)
    -> CodeGen (IROpenAcc Native aenv (Array DIM2 c))
mkStencil22DMiddle _ aenv f b1 ir1@(IRManifest v1) b2 ir2@(IRManifest v2) =
  let
      (y0,y1,x0,x1, paramGang) = gangParam2D
      (arrOut, paramOut)       = mutableArray ("out" :: Name (Array DIM2 c))
      paramEnv                 = envParam aenv
  in
  makeOpenAcc "stencil22DMiddle" (paramGang ++ paramOut ++ paramEnv) $ do
    yrange    <- sub numType y1 y0
    remainder <- A.rem integralType yrange (int 4)
    y'        <- sub numType y1 remainder
    --
    imapFromStepTo y0 (int 4) y' $ \y -> do
      y_1 <- add numType y (int 1)
      y_2 <- add numType y (int 2)
      y_3 <- add numType y (int 3)
      imapFromTo x0 x1 $ \x -> do
        let ix = index2D x y
        i0 <- intOfIndex (irArrayShape arrOut) ix
        i1 <- intOfIndex (irArrayShape arrOut) (index2D x y_1)
        i2 <- intOfIndex (irArrayShape arrOut) (index2D x y_2)
        i3 <- intOfIndex (irArrayShape arrOut) (index2D x y_3)
        (s10, s11, s12, s13) <- stencilAccesses Nothing (irArray (aprj v1 aenv)) ix
        (s20, s21, s22, s23) <- stencilAccesses Nothing (irArray (aprj v2 aenv)) ix
        r0 <- app2 f s10 s20
        r1 <- app2 f s11 s21
        r2 <- app2 f s12 s22
        r3 <- app2 f s13 s23
        writeArray arrOut i0 r0
        writeArray arrOut i1 r1
        writeArray arrOut i2 r2
        writeArray arrOut i3 r3
    -- Do the last few rows that aren't in the groups of 4.
    imapFromTo y' y1 $ \y ->
      imapFromTo x0 x1 $ \x ->
        middleElement2 b1 b2 aenv f ir1 ir2 arrOut x y

    return_


mkStencil22DLeftRight
    :: forall aenv stencil1 stencil2 a b c.
       (Stencil DIM2 a stencil1, Stencil DIM2 b stencil2, Elt c, Skeleton Native)
    => Native
    -> Gamma aenv
    -> IRFun2 Native aenv (stencil1 -> stencil2 -> c)
    -> Boundary (IR a)
    -> IRManifest Native aenv (Array DIM2 a)
    -> Boundary (IR b)
    -> IRManifest Native aenv (Array DIM2 b)
    -> CodeGen (IROpenAcc Native aenv (Array DIM2 c))
mkStencil22DLeftRight _ aenv f b1 ir1 b2 ir2 =
  let
      (start, end, borderWidth, _borderHeight, width, _height, paramGang) = gangParam2DSides
      (arrOut, paramOut) = mutableArray ("out" :: Name (Array DIM2 c))
      paramEnv           = envParam aenv
  in
  makeOpenAcc "stencil22DLeftRight" (paramGang ++ paramOut ++ paramEnv) $ do
    imapFromTo (int 0) borderWidth $ \x -> do
      rightx <- sub numType width =<< add numType (int 1) x
      imapFromTo start end $ \y -> do
        -- Left
        boundaryElement2 b1 b2 aenv f ir1 ir2 arrOut x y
        -- Right
        boundaryElement2 b1 b2 aenv f ir1 ir2 arrOut rightx y

    return_


mkStencil22DTopBottom
    :: forall aenv stencil1 stencil2 a b c.
       (Stencil DIM2 a stencil1, Stencil DIM2 b stencil2, Elt c, Skeleton Native)
    => Native
    -> Gamma aenv
    -> IRFun2 Native aenv (stencil1 -> stencil2 -> c)
    -> Boundary (IR a)
    -> IRManifest Native aenv (Array DIM2 a)
    -> Boundary (IR b)
    -> IRManifest Native aenv (Array DIM2 b)
    -> CodeGen (IROpenAcc Native aenv (Array DIM2 c))
mkStencil22DTopBottom _ aenv f b1 ir1 b2 ir2 =
  let
      (start, end, _borderWidth, borderHeight, _width, height, paramGang) = gangParam2DSides
      (arrOut, paramOut) = mutableArray ("out" :: Name (Array DIM2 c))
      paramEnv           = envParam aenv
  in
  makeOpenAcc "stencil22DTopBottom" (paramGang ++ paramOut ++ paramEnv) $ do
    imapFromTo (int 0) borderHeight $ \y -> do
      bottomy <- sub numType height =<< add numType (int 1) y
      imapFromTo start end $ \x -> do
        -- Top
        boundaryElement2 b1 b2 aenv f ir1 ir2 arrOut x y
        -- Bottom
        boundaryElement2 b1 b2 aenv f ir1 ir2 arrOut x bottomy

    return_
