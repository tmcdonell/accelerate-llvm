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
mkStencil1 n aenv f b1 ir1@(IRManifest v1)
  | Just Refl <- matchShapeType (undefined :: DIM2) (undefined :: sh)
  = mkStencil_2D "stencil1" (Just b1) Nothing aenv $
      \mB1 ix -> do
        sten <- stencilAccess mB1 (irArray (aprj v1 aenv)) ix
        app1 f sten
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
mkStencil2 n aenv f b1 ir1@(IRManifest v1) b2 ir2@(IRManifest v2)
  | Just Refl <- matchShapeType (undefined :: DIM2) (undefined :: sh)
  = mkStencil_2D "stencil2" (Just b1, Just b2) (Nothing, Nothing) aenv $
      \(mB1, mB2) ix -> do
        sten1 <- stencilAccess mB1 (irArray (aprj v1 aenv)) ix
        sten2 <- stencilAccess mB2 (irArray (aprj v2 aenv)) ix
        app2 f sten1 sten2
  --
  | otherwise
  = defaultStencil2 n aenv f b1 ir1 b2 ir2


mkStencil_2D
  :: Elt e
  => ShortByteString
  -> bounds
  -> bounds
  -> Gamma aenv1
  -> (bounds -> IR DIM2 -> CodeGen (IR e))
  -> CodeGen (IROpenAcc Native aenv a)
mkStencil_2D stencilN jBounds nBounds aenv stenElem =
  let
      (start, end, borderWidth, borderHeight, width, height, paramGang) = gangParam2D
      (arrOut, paramOut) = mutableArray ("out" :: Name (Array DIM2 b))
      paramEnv           = envParam aenv
      params = paramGang ++ paramOut ++ paramEnv
      unrollN = 4
      --
      evalElem bounds (IR x) (IR y) = do
        let ix = IR (OP_Pair (OP_Pair OP_Unit y) x)
        i <- intOfIndex (irArrayShape arrOut) ix
        writeArray arrOut i =<< stenElem bounds ix
  in
    foldr1 (+++) <$> sequence
      --
      [ makeOpenAcc (Label $ stencilN <> "_2D_LeftRight") params $ do
          imapFromTo (int 0) borderWidth $ \x -> do
            rightx <- sub numType width =<< add numType (int 1) x
            imapFromTo start end $ \y -> do
              -- Left
              evalElem jBounds x      y
              -- Right
              evalElem jBounds rightx y

          return_
      --
      , makeOpenAcc (Label $ stencilN <> "_2D_TopBottom") params $ do
          imapFromTo (int 0) borderHeight $ \y -> do
            bottomy <- sub numType height =<< add numType (int 1) y
            imapFromTo start end $ \x -> do
              -- Top
              evalElem jBounds x y
              -- Bottom
              evalElem jBounds x bottomy

          return_
      --
      , makeOpenAcc (Label $ stencilN <> "_2D_Middle") params $ do
          let (y0, y1, x0) = (start, end, borderWidth)
          x1        <- sub numType width x0
          yrange    <- sub numType y1 y0
          remainder <- A.rem integralType yrange (int unrollN)
          y'        <- sub numType y1 remainder
          -- Evaluate most rows in groups of 4
          imapFromStepTo y0 (int unrollN) y' $ \y -> do
            ys <- forM [1..(unrollN-1)] $ \dy -> add numType y (int dy)
            imapFromTo x0 x1 $ \x -> do
              forM_ (y:ys) $ \y_tile -> do
                evalElem nBounds x y_tile
          -- Evaluate the remaining rows singularly
          imapFromTo y' y1 $ \y ->
            imapFromTo x0 x1 $ \x ->
              evalElem nBounds x y

          return_
      --
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
