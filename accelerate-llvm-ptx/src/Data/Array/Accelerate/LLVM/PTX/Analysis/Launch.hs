{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators   #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.Analysis.Launch
-- Copyright   : [2008..2017] Manuel M T Chakravarty, Gabriele Keller
--               [2009..2018] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.Analysis.Launch (

  DeviceProperties, Occupancy, LaunchConfig,
  simpleLaunchConfig, launchConfig,
  multipleOf, multipleOfQ,

  launchConfigDIM2,
  launchConfigDIM3,

) where

import Data.Array.Accelerate.Array.Sugar                            ( Z(..), (:.)(..), DIM2 )
import Data.Array.Accelerate.Error

import Foreign.CUDA.Analysis                                        as CUDA

import Control.Lens
import Language.Haskell.TH


-- | Given information about the resource usage of the compiled kernel,
-- determine the optimum launch parameters.
--
type LaunchConfig
  =  Int                            -- maximum #threads per block
  -> Int                            -- #registers per thread
  -> Int                            -- #bytes of static shared memory
  -> ( Occupancy
     , Int                          -- thread block size
     , Int -> Int                   -- grid size required to process the given input size
     , Int                          -- #bytes dynamic shared memory
     , Q (TExp (Int -> Int))
     )

-- | Analytics for a simple kernel which requires no additional shared memory or
-- have other constraints on launch configuration. The smallest thread block
-- size, in increments of a single warp, with the highest occupancy is used.
--
simpleLaunchConfig :: DeviceProperties -> LaunchConfig
simpleLaunchConfig dev = launchConfig dev (decWarp dev) (const 0) multipleOf multipleOfQ


-- | Determine the optimal kernel launch configuration for a kernel.
--
launchConfig
    :: DeviceProperties             -- ^ Device architecture to optimise for
    -> [Int]                        -- ^ Thread block sizes to consider
    -> (Int -> Int)                 -- ^ Shared memory (#bytes) as a function of thread block size
    -> (Int -> Int -> Int)          -- ^ Determine grid size for input size 'n' (first arg) over thread blocks of size 'm' (second arg)
    -> Q (TExp (Int -> Int -> Int))
    -> LaunchConfig
launchConfig dev candidates dynamic_smem grid_size grid_sizeQ maxThreads registers static_smem =
  let
      (cta, occ)  = optimalBlockSizeOf dev (filter (<= maxThreads) candidates) (const registers) smem
      maxGrid     = multiProcessorCount dev * activeThreadBlocks occ
      grid n      = maxGrid `min` grid_size n cta
      smem n      = static_smem + dynamic_smem n
      gridQ       = [|| \n -> (maxGrid::Int) `min` $$grid_sizeQ (n::Int) (cta::Int) ||]
  in
  ( occ, cta, grid, dynamic_smem cta, gridQ )


-- | The next highest multiple of 'y' from 'x'.
--
multipleOf :: Int -> Int -> Int
multipleOf x y = ((x + y - 1) `quot` y)

multipleOfQ :: Q (TExp (Int -> Int -> Int))
multipleOfQ = [|| multipleOf ||]



-- | Reconfigure the kernel launch to process as a 2-dimensional iteration
-- space.
--
-- XXX: The target grid size is for this number of elements as a linear
--      iteration space, which may not be a useful metric once the thread blocks
--      are processing in multiple dimensions.
--
launchConfigDIM2
    :: Int                        -- grid size
    -> Int                        -- thread block size
    -> DIM2                       -- dimensions of the iteration space
    -> ( (Int,Int,Int)            -- grid dimensions
       , (Int,Int,Int)            -- thread block dimensions
       )
launchConfigDIM2 ncta cta sh@(Z :. y :. x) = (balance gd0, bd)
  where
    (bdX, bdY) = blockSizeDIM2 cta sh

    nctaX = x `multipleOf` bdX
    nctaY = y `multipleOf` bdY
    grid  = (nctaX, nctaY, 1)
    gd0   = (ncta, 1, 1)
    bd    = (bdX, bdY, 1)

    balance gd
      | Just gd' <- rebalance grid gd _1 _2 = balance gd'
      | Just gd' <- rebalance grid gd _2 _1 = balance gd'
      | otherwise                           = gd


-- | Reconfigure the kernel launch to process as a 3+-dimensional iteration
-- space.
--
launchConfigDIM3
    :: Int                        -- grid size
    -> Int                        -- thread block size
    -> (sh :. Int :. Int :. Int)  -- dimensions of the iteration space
    -> ( (Int,Int,Int)            -- grid dimensions
       , (Int,Int,Int)            -- thread block dimensions
       )
launchConfigDIM3 ncta cta sh@(_ :. z :. y :. x) = (balance gd0, bd)
  where
    bd@(bdX, bdY, bdZ)  = blockSizeDIM3 cta sh

    nctaX = x `multipleOf` bdX
    nctaY = y `multipleOf` bdY
    nctaZ = z `multipleOf` bdZ
    grid  = (nctaX, nctaY, nctaZ)
    gd0   = (ncta, 1, 1)

    balance gd
      | Just gd' <- rebalance grid gd _1 _3 = balance gd'
      | Just gd' <- rebalance grid gd _1 _2 = balance gd'
      | Just gd' <- rebalance grid gd _2 _3 = balance gd'
      | Just gd' <- rebalance grid gd _2 _1 = balance gd'
      | Just gd' <- rebalance grid gd _3 _2 = balance gd'
      | Just gd' <- rebalance grid gd _3 _1 = balance gd'
      | otherwise                           = gd


-- Determine an appropriate 2-dimensional thread block size containing the given
-- number of threads in the (x, y) dimensions respectively, to evaluate the
-- given iteration space. The second argument is useful because the thread block
-- dimensions will be rebalanced for highly skewed iteration spaces.
--
blockSizeDIM2 :: Int -> DIM2 -> (Int,Int)
blockSizeDIM2 cta (Z :. y :. x) = balance bd0
  where
    sh              = (x,y)
    bd0
      | cta <= 256  = (16, quot cta 16)
      | cta <= 1024 = (32, quot cta 32)
      | otherwise   = $internalError "blockSizeDIM2" "expected fewer than 1024 threads per block"

    balance bd
      | Just bd' <- rebalance sh bd _1 _2 = balance bd'
      | Just bd' <- rebalance sh bd _2 _1 = balance bd'
      | otherwise                         = bd

-- Determine an appropriate 3-dimensional thread block size containing the given
-- number of threads in the (x, y, z) dimensions, respectively.
--
blockSizeDIM3 :: Int -> (sh :. Int :. Int :. Int) -> (Int,Int,Int)
blockSizeDIM3 cta (_ :. z :. y :. x) = balance bd0
  where
    sh              = (x,y,z)
    bd0
      | cta <= 256  = (16, quot cta 16, 1)
      | cta <= 1024 = (32, quot cta 32, 1)
      | otherwise   = $internalError "blockSizeDIM3" "expected fewer than 1024 threads per block"

    balance bd
      | Just bd' <- rebalance sh bd _1 _3 = balance bd'
      | Just bd' <- rebalance sh bd _1 _2 = balance bd'
      | Just bd' <- rebalance sh bd _2 _3 = balance bd' -- NB: prefer to shrink z rather than x
      | Just bd' <- rebalance sh bd _2 _1 = balance bd'
      | Just bd' <- rebalance sh bd _3 _2 = balance bd' -- NB: prefer to shrink y rather than x
      | Just bd' <- rebalance sh bd _3 _1 = balance bd'
      | otherwise                         = bd

    -- gd0 = case cta of
    --         32   -> (16, 2, 1)
    --         64   -> (16, 2, 2)
    --         96   -> (16, 3, 2)
    --         128  -> (16, 4, 2)
    --         160  -> (16, 5, 2)
    --         192  -> (16, 6, 2)
    --         224  -> (16, 7, 2)
    --         256  -> (16, 4, 4)
    --         288  -> (16, 9, 2)
    --         320  -> (16, 5, 4)
    --         352  -> (16,11, 2)
    --         384  -> (16, 6, 4)
    --         416  -> (16,13, 2)
    --         448  -> (16, 7, 4)
    --         480  -> (16,15, 2)
    --         512  -> (32, 4, 4)
    --         544  -> (16,17, 2)
    --         576  -> (16, 9, 4)
    --         608  -> (16,19, 2)
    --         640  -> (32, 5, 4)
    --         672  -> (16,21, 2)
    --         704  -> (32,11, 2)
    --         736  -> (16,23, 2)
    --         768  -> (32, 6, 4)
    --         800  -> (32, 5, 5)
    --         832  -> (32,13, 2)
    --         864  -> (16,27, 2)
    --         896  -> (16, 8, 7)
    --         928  -> (16,29, 2)
    --         960  -> (32,15, 2)
    --         992  -> (16,31, 2)
    --         1024 -> (32, 8, 4)
    --         _    -> $internalError "blockSizeDIM3" "expected fewer than 1024 threads per block"

rebalance :: a -> a -> Lens' a Int -> Lens' a Int -> Maybe a
rebalance target current dst src
  | target ^. src < current ^. src
  , target ^. dst > current ^. dst
  , Just (p,q)  <- pdiv (current ^. src)
  , target ^. src <= q
  = Just $ set src q $ current & dst *~ p
  --
  | otherwise
  = Nothing

-- Attempt to divide by the smallest prime number (<32); if successful returns
-- the divisor and quotient.
--
pdiv :: Int -> Maybe (Int, Int)
pdiv x = go primes
  where
    primes        = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
    --
    go []         = Nothing
    go (p:ps)
      | r == 0    = Just (p,q)
      | otherwise = go ps
      where
        (q,r) = quotRem x p

