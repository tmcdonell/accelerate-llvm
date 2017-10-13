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

import Control.Monad

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

import Data.ByteString.Short
import Data.Monoid

import qualified LLVM.AST.Global                                    as LLVM
import           LLVM.AST.Type.Name


mkStencil1
    :: forall aenv stencil a b sh. (Stencil sh a stencil, Elt b, Skeleton Native)
    => Native
    -> Gamma aenv
    -> IRFun1 Native aenv (stencil -> b)
    -> Boundary (IR a)
    -> IRManifest Native aenv (Array sh a)
    -> CodeGen (IROpenAcc Native aenv (Array sh b))
mkStencil1 n aenv f b1 ir1
  | Just Refl <- matchShapeType (undefined :: DIM2) (undefined :: sh)
  = mkStencil_2D "stencil1" stencilElement (Just b1) Nothing aenv f ir1
  | otherwise
  = defaultStencil1 n aenv f b1 ir1


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
mkStencil2 n aenv f b1 ir1 b2 ir2
  | Just Refl <- matchShapeType (undefined :: DIM2) (undefined :: sh)
  = mkStencil_2D "stencil2" stencilElement2 (Just b1, Just b2) (Nothing, Nothing) aenv f (ir1, ir2)
  | otherwise
  = defaultStencil2 n aenv f b1 ir1 b2 ir2


mkStencil_2D 
  :: Elt e
     => ShortByteString
     -> (t2
        -> Gamma aenv1
        -> t1
        -> t
        -> IRArray (Array DIM2 e)
        -> IR Int
        -> IR Int
        -> CodeGen ())
     -> t2
     -> t2
     -> Gamma aenv1
     -> t1
     -> t
     -> CodeGen (IROpenAcc Native aenv a)
mkStencil_2D stencilN stenElem jBounds nBounds aenv f irs =
  foldr1 (+++) <$> sequence
    [ mkStencil2DLeftRight stencilN stenElem jBounds aenv f irs
    , mkStencil2DTopBottom stencilN stenElem jBounds aenv f irs
    , mkStencil2DMiddle    stencilN stenElem nBounds aenv f irs
    ]
    

gangParam2D :: ( IR Int, IR Int, IR Int
               , IR Int, IR Int, IR Int, [LLVM.Parameter])
gangParam2D =
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
    :: forall aenv stencil a b. (Stencil DIM2 a stencil, Elt b)
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
       (Stencil DIM2 a stencil1, Stencil DIM2 b stencil2, Elt c)
    => (Maybe (Boundary (IR a)), Maybe (Boundary (IR b)))
    -> Gamma aenv
    -> IRFun2 Native aenv (stencil1 -> stencil2 -> c)
    -> (IRManifest Native aenv (Array DIM2 a), IRManifest Native aenv (Array DIM2 b))
    -> IRArray (Array DIM2 c)
    -> IR Int
    -> IR Int
    -> CodeGen ()
stencilElement2 (mB1, mB2) aenv f ((IRManifest v1), (IRManifest v2)) arrOut x y = do
  let ix = index2D x y
  i     <- intOfIndex (irArrayShape arrOut) ix
  sten1 <- stencilAccess mB1 (irArray (aprj v1 aenv)) ix
  sten2 <- stencilAccess mB2 (irArray (aprj v2 aenv)) ix
  r     <- app2 f sten1 sten2
  writeArray arrOut i r  


mkStencil2DMiddle
  :: Elt e
  => ShortByteString
     -> (t2
        -> Gamma aenv1
        -> t1
        -> t
        -> IRArray (Array DIM2 e)
        -> IR Int
        -> IR Int
        -> CodeGen ())
     -> t2
     -> Gamma aenv1
     -> t1
     -> t
     -> CodeGen (IROpenAcc Native aenv a)
mkStencil2DMiddle stencilN stenElem bounds aenv f irs =
  let
      (y0, y1, x0, _borderHeight, width, _height, paramGang) = gangParam2D
      (arrOut, paramOut) = mutableArray ("out" :: Name (Array DIM2 b))
      paramEnv           = envParam aenv
  in
  makeOpenAcc (Label $ stencilN <> "_2D_Middle") (paramGang ++ paramOut ++ paramEnv) $ do
    x1        <- sub numType width x0
    yrange    <- sub numType y1 y0
    remainder <- A.rem integralType yrange (int 4)
    y'        <- sub numType y1 remainder
    --
    imapFromStepTo y0 (int 4) y' $ \y -> do
      ys <- forM [1..3] $ \dy -> add numType y (int dy)
      imapFromTo x0 x1 $ \x -> do
        forM_ (y:ys) $ \y_tile -> do
          stenElem bounds aenv f irs arrOut x y_tile
    -- Do the last few rows that aren't in the groups of 4.
    imapFromTo y' y1 $ \y ->
      imapFromTo x0 x1 $ \x ->
        stenElem bounds aenv f irs arrOut x y

    return_


mkStencil2DLeftRight
  :: Elt e
  => ShortByteString
     -> (t2
        -> Gamma aenv1
        -> t1
        -> t
        -> IRArray (Array DIM2 e)
        -> IR Int
        -> IR Int
        -> CodeGen ())
     -> t2
     -> Gamma aenv1
     -> t1
     -> t
     -> CodeGen (IROpenAcc Native aenv a)
mkStencil2DLeftRight stencilN stenElem bounds aenv f irs =
  let
      (start, end, borderWidth, _borderHeight, width, _height, paramGang) = gangParam2D
      (arrOut, paramOut) = mutableArray ("out" :: Name (Array DIM2 b))
      paramEnv           = envParam aenv
  in
  makeOpenAcc (Label $ stencilN <> "_2D_LeftRight") (paramGang ++ paramOut ++ paramEnv) $ do
    imapFromTo (int 0) borderWidth $ \x -> do
      rightx <- sub numType width =<< add numType (int 1) x
      imapFromTo start end $ \y -> do
        -- Left
        stenElem bounds aenv f irs arrOut x y
        -- Right
        stenElem bounds aenv f irs arrOut rightx y

    return_


mkStencil2DTopBottom
  :: Elt e
  => ShortByteString
  -> (t2
     -> Gamma aenv1
     -> t1
     -> t
     -> IRArray (Array DIM2 e)
     -> IR Int
     -> IR Int
     -> CodeGen ())
  -> t2
  -> Gamma aenv1
  -> t1
  -> t
  -> CodeGen (IROpenAcc Native aenv a)
mkStencil2DTopBottom stencilN stenElem bounds aenv f irs =
  let
      (start, end, _borderWidth, borderHeight, _width, height, paramGang) = gangParam2D
      (arrOut, paramOut) = mutableArray ("out" :: Name (Array DIM2 b))
      paramEnv           = envParam aenv
  in
  makeOpenAcc (Label $ stencilN <> "_2D_TopBottom") (paramGang ++ paramOut ++ paramEnv) $ do
    imapFromTo (int 0) borderHeight $ \y -> do
      bottomy <- sub numType height =<< add numType (int 1) y
      imapFromTo start end $ \x -> do
        -- Top
        stenElem bounds aenv f irs arrOut x y
        -- Bottom
        stenElem bounds aenv f irs arrOut x bottomy

    return_
