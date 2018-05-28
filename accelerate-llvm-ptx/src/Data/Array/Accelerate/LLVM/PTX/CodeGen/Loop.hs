{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.CodeGen.Loop
-- Copyright   : [2015..2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.CodeGen.Loop (

  imapFromTo32,     imapFromTo64,
  imapNestFromTo32, imapNestFromTo64,

) where

-- accelerate
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Type

import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic            as A
import Data.Array.Accelerate.LLVM.CodeGen.Exp
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import qualified Data.Array.Accelerate.LLVM.CodeGen.Loop        as Loop

import Data.Array.Accelerate.LLVM.PTX.CodeGen.Base


-- | A standard loop where the CUDA threads cooperatively step over an index
-- space from the start to end indices. The threads stride the array in a way
-- that maintains memory coalescing.
--
-- The start and end array indices are given as natural array indexes, and the
-- thread specific indices are calculated by the loop.
--
-- > for ( int i = blockDim.x * blockIdx.x + threadIdx.x + start
-- >     ; i <  end
-- >     ; i += blockDim.x * gridDim.x )
--
-- TODO: This assumes that the starting offset retains alignment to the warp
--       boundary. This might not always be the case, so provide a version that
--       explicitly aligns reads to the warp boundary.
--
imapFromTo64 :: IR Int -> IR Int -> (IR Int -> CodeGen ()) -> CodeGen ()
imapFromTo64 = imapFromToUsing (int =<< gridSize_x) (int =<< globalThreadIdx_x)

imapFromTo32 :: IR Int32 -> IR Int32 -> (IR Int32 -> CodeGen ()) -> CodeGen ()
imapFromTo32 = imapFromToUsing gridSize_x globalThreadIdx_x

imapFromToUsing
    :: (IsIntegral i, Elt i)
    => CodeGen (IR i)
    -> CodeGen (IR i)
    -> IR i
    -> IR i
    -> (IR i -> CodeGen ())
    -> CodeGen ()
imapFromToUsing gridSize threadIdx start end body = do
  step  <- gridSize
  tid   <- threadIdx
  i0    <- add numType tid start
  --
  Loop.imapFromStepTo i0 step end body


int :: IsIntegral i => IR i -> CodeGen (IR Int)
int = A.fromIntegral integralType numType

-- | Generate a series of nested 'for' loops which iterate between the start and
-- end indices of a given hyper-rectangle.
--
-- The inner three dimensions will use the thread block/grid indices to stride
-- the index space.
--
-- The imapaNestFrom32 version keeps the loop indices as 32-bit counters in
-- order to (greatly) reduce register pressure. Note however that the incoming
-- and outgoing shapes are always treated as standard 'Int's, so some
-- conversions are required.
--
imapNestFromTo32
    :: forall sh. Shape sh
    => IR sh                                    -- ^ initial index (inclusive)
    -> IR sh                                    -- ^ final index (exclusive)
    -> IR sh                                    -- ^ total array extent
    -> (IR sh -> IR Int -> CodeGen ())          -- ^ apply at each index
    -> CodeGen ()
imapNestFromTo32 (IR start) (IR end) extent body =
  go (rank (undefined::sh)) (eltType (undefined::sh)) start end (body' . IR)
  where
    body' ix = body ix =<< intOfIndex extent ix

    i32 :: IR Int -> CodeGen (IR Int32)
    i32 v = A.fromIntegral integralType numType v

    go :: Int -> TupleType t -> Operands t -> Operands t -> (Operands t -> CodeGen ()) -> CodeGen ()
    go 0 TypeRunit OP_Unit OP_Unit k
      = k OP_Unit

    go r (TypeRpair tsh tsz) (OP_Pair ssh ssz) (OP_Pair esh esz) k
      | TypeRscalar t <- tsz
      , Just Refl     <- matchScalarType t (scalarType :: ScalarType Int)
      = go (r-1) tsh ssh esh
      $ \sz -> do
          u <- i32 (IR ssz)
          v <- i32 (IR esz)
          case r of
            1 -> imapFromToUsing gridSize_x globalThreadIdx_x u v $ \i -> do IR j <- int i; k (OP_Pair sz j)
            2 -> imapFromToUsing gridSize_y globalThreadIdx_y u v $ \i -> do IR j <- int i; k (OP_Pair sz j)
            3 -> imapFromToUsing gridSize_z globalThreadIdx_z u v $ \i -> do IR j <- int i; k (OP_Pair sz j)
            _ -> Loop.imapFromStepTo u (lift 1 :: IR Int32) v     $ \i -> do IR j <- int i; k (OP_Pair sz j)

    go _ _ _ _ _
      = $internalError "imapNestFromTo" "expected shape with Int components"

imapNestFromTo64
    :: forall sh. Shape sh
    => IR sh                                    -- ^ initial index (inclusive)
    -> IR sh                                    -- ^ final index (exclusive)
    -> IR sh                                    -- ^ total array extent
    -> (IR sh -> IR Int -> CodeGen ())          -- ^ apply at each index
    -> CodeGen ()
imapNestFromTo64 (IR start) (IR end) extent body =
  go (rank (undefined::sh)) (eltType (undefined::sh)) start end (body' . IR)
  where
    body' ix = body ix =<< intOfIndex extent ix

    go :: Int -> TupleType t -> Operands t -> Operands t -> (Operands t -> CodeGen ()) -> CodeGen ()
    go 0 TypeRunit OP_Unit OP_Unit k
      = k OP_Unit

    go r (TypeRpair tsh tsz) (OP_Pair ssh ssz) (OP_Pair esh esz) k
      | TypeRscalar t <- tsz
      , Just Refl     <- matchScalarType t (scalarType :: ScalarType Int)
      = go (r-1) tsh ssh esh
      $ \sz     -> case r of
                     1 -> imapFromToUsing (int =<< gridSize_x) (int =<< globalThreadIdx_x) (IR ssz) (IR esz)
                     2 -> imapFromToUsing (int =<< gridSize_y) (int =<< globalThreadIdx_y) (IR ssz) (IR esz)
                     3 -> imapFromToUsing (int =<< gridSize_z) (int =<< globalThreadIdx_z) (IR ssz) (IR esz)
                     _ -> Loop.imapFromStepTo (IR ssz) (lift 1 :: IR Int) (IR esz)
      $ \(IR i) -> k (OP_Pair sz i)

    go _ _ _ _ _
      = $internalError "imapNestFromTo" "expected shape with Int components"

