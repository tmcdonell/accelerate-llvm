{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE MagicHash           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Array.Data
-- Copyright   : [2014..2018] Trevor L. McDonell
--               [2014..2014] Vinod Grover (NVIDIA Corporation)
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Array.Data (

  Remote(..),
  newRemote, newRemoteAsync,
  useRemote,
  copyToRemote,
  copyToHost,
  copyToPeer,
  indexRemote,

  runIndexArray, runIndexArrayAsync,
  runArray, runArrayAsync,
  runArrays, runArraysAsync,

  module Data.Array.Accelerate.Array.Data,

) where

-- accelerate
import Data.Array.Accelerate.Array.Data
import Data.Array.Accelerate.Array.Sugar
import qualified Data.Array.Accelerate.Array.Representation         as R

import Data.Array.Accelerate.LLVM.Execute.Async

-- standard library
import Control.Monad                                                ( liftM, liftM2 )
import Data.Typeable
import Foreign.Ptr
import Foreign.Storable
import Prelude

import GHC.Int                                                      ( Int(..) )


class Async arch => Remote arch where

  -- | Allocate a new uninitialised array on the remote device.
  --
  allocateRemote :: (Shape sh, Elt e) => sh -> Par arch (Array sh e)

  -- | Use the given immutable array on the remote device. Since the source
  -- array is immutable, the garbage collector can evict and re-upload the data
  -- as necessary without copy-back.
  --
  {-# INLINE useRemoteR #-}
  useRemoteR
      :: (ArrayElt e, ArrayPtrs e ~ Ptr a, Storable a, Typeable a, Typeable e)
      => Int                      -- ^ number of elements to copy
      -> ArrayData e              -- ^ array payload
      -> Par arch (FutureR arch (ArrayData e))
  useRemoteR _ = newFull

  -- | Upload an array from the host to the remote device.
  --
  {-# INLINE copyToRemoteR #-}
  copyToRemoteR
      :: (ArrayElt e, ArrayPtrs e ~ Ptr a, Storable a, Typeable a, Typeable e)
      => Int                      -- ^ number of elements to copy
      -> ArrayData e              -- ^ array payload
      -> Par arch (FutureR arch (ArrayData e))
  copyToRemoteR _ = newFull

  -- | Copy an array from the remote device back to the host.
  --
  {-# INLINE copyToHostR #-}
  copyToHostR
      :: (ArrayElt e, ArrayPtrs e ~ Ptr a, Storable a, Typeable a, Typeable e)
      => Int                      -- ^ number of elements to copy
      -> ArrayData e              -- ^ array payload
      -> Par arch (FutureR arch (ArrayData e))
  copyToHostR _ = newFull

  -- | Copy a section of an array between two remote instances of the same type.
  -- This may be more efficient than copying to the host and then to the second
  -- remote instance (e.g. DMA between two CUDA devices).
  --
  {-# INLINE copyToPeerR #-}
  copyToPeerR
      :: (ArrayElt e, ArrayPtrs e ~ Ptr a, Storable a, Typeable a, Typeable e)
      => arch                     -- ^ remote device to copy to
      -> Int                      -- ^ number of elements to copy
      -> ArrayData e              -- ^ array payload
      -> Par arch (FutureR arch (ArrayData e))
  copyToPeerR _ _ = newFull

  -- | Upload an immutable array from the host to the remote device,
  -- asynchronously. Since the source array is immutable, the garbage collector
  -- can evict and re-upload the data as necessary without copy-back. This may
  -- upload each array payload in a separate execution stream, thereby making us
  -- of multiple memcpy engines.
  --
  {-# INLINE useRemoteAsync #-}
  useRemoteAsync :: Arrays arrs => arrs -> Par arch (FutureR arch arrs)
  useRemoteAsync arrs =
    runArraysAsync arrs $ \arr@(Array sh _) ->
      let n = R.size sh
      in  runArrayAsync arr $ \m ad ->
            useRemoteR (n*m) ad

  -- | Upload an existing array to the remote device, asynchronously.
  --
  {-# INLINE copyToRemoteAsync #-}
  copyToRemoteAsync :: Arrays arrs => arrs -> Par arch (FutureR arch arrs)
  copyToRemoteAsync arrs =
    runArraysAsync arrs $ \arr@(Array sh _) ->
      let n = R.size sh
      in  runArrayAsync arr $ \m ad ->
            copyToRemoteR (n*m) ad

  -- | Copy an array from the remote device to the host, asynchronously
  --
  {-# INLINE copyToHostAsync #-}
  copyToHostAsync :: Arrays arrs => arrs -> Par arch (FutureR arch arrs)
  copyToHostAsync arrs =
    runArraysAsync arrs $ \arr@(Array sh _) ->
      let n = R.size sh
      in  runArrayAsync arr $ \m ad ->
            copyToHostR (n*m) ad

  -- | Copy arrays between two remote instances. This may be more efficient than
  -- copying to the host and then to the second remote instance (e.g. by DMA
  -- between the two remote devices).
  --
  {-# INLINE copyToPeerAsync #-}
  copyToPeerAsync :: Arrays arrs => arch -> arrs -> Par arch (FutureR arch arrs)
  copyToPeerAsync peer arrs =
    runArraysAsync arrs $ \arr@(Array sh _) ->
      let n = R.size sh
      in  runArrayAsync arr $ \m ad ->
            copyToPeerR peer (n*m) ad

  -- | Read a single element from the array at the given row-major index
  --
  {-# INLINE indexRemoteAsync #-}
  indexRemoteAsync
      :: Array sh e
      -> Int
      -> Par arch (FutureR arch e)
  indexRemoteAsync (Array _ ad) i = newFull (toElt $ unsafeIndexArrayData ad i)


-- | Create a new array from its representation on the host, and upload it to
-- the remote device.
--
{-# INLINE newRemote #-}
newRemote
    :: (Remote arch, Shape sh, Elt e)
    => sh
    -> (sh -> e)
    -> Par arch (Array sh e)
newRemote sh f =
  get =<< newRemoteAsync sh f


-- | Create a new array from its representation on the host, and upload it as
-- a new remote array, asynchronously.
--
{-# INLINE newRemoteAsync #-}
newRemoteAsync
    :: (Remote arch, Shape sh, Elt e)
    => sh
    -> (sh -> e)
    -> Par arch (FutureR arch (Array sh e))
newRemoteAsync sh f =
  useRemoteAsync $! fromFunction sh f


-- | Upload an immutable array from the host to the remote device. This is
-- a synchronous operation in that it will not return until the transfer
-- completes, but the individual array payloads will be uploaded concurrently if
-- possible.
--
{-# INLINE useRemote #-}
useRemote :: (Remote arch, Arrays a) => a -> Par arch a
useRemote arrs =
  get =<< useRemoteAsync arrs

-- | Uploading existing arrays from the host to the remote device. This is
-- synchronous with respect to the calling thread, but the individual array
-- payloads may themselves be transferred concurrently.
--
{-# INLINE copyToRemote #-}
copyToRemote :: (Remote arch, Arrays a) => a -> Par arch a
copyToRemote arrs =
  get =<< copyToRemoteAsync arrs

-- | Copy an array from the remote device to the host. This is synchronous with
-- respect to the calling thread, but the individual array payloads may
-- themselves be transferred concurrently.
--
{-# INLINE copyToHost #-}
copyToHost :: (Remote arch, Arrays a) => a -> Par arch a
copyToHost arrs =
  block =<< copyToHostAsync arrs

-- | Copy arrays between two remote instances of the same type. This may be more
-- efficient than copying to the host and then to the second remote instance
-- (e.g. DMA between CUDA devices).
--
{-# INLINE copyToPeer #-}
copyToPeer :: (Remote arch, Arrays a) => arch -> a -> Par arch a
copyToPeer peer arrs = do
  get =<< copyToPeerAsync peer arrs

-- | Read a single element from the remote array at the given row-major index.
-- This is synchronous with respect to both the host and remote device.
--
{-# INLINE indexRemote #-}
indexRemote :: Remote arch => Array sh e -> Int -> Par arch e
indexRemote arr i =
  block =<< indexRemoteAsync arr i


-- Helpers for traversing the Arrays data structure
-- ------------------------------------------------

-- | Read a single element from an array at the given row-major index.
--
{-# INLINE runIndexArray #-}
runIndexArray
    :: forall m sh e. Monad m
    => (forall s a. (ArrayElt s, ArrayPtrs s ~ Ptr a, Storable a, Typeable a, Typeable s) => ArrayData s -> Int -> Int -> m (ArrayData s))
    -> Array sh e
    -> Int
    -> m e
runIndexArray worker (Array _ adata) i = toElt . flip unsafeIndexArrayData 0 <$> indexR arrayElt adata 1
  where
    indexR :: ArrayEltR s -> ArrayData s -> Int -> m (ArrayData s)
    indexR ArrayEltRunit    !_  !_ = return AD_Unit
    indexR ArrayEltRint     !ad !n = worker ad i n
    indexR ArrayEltRint8    !ad !n = worker ad i n
    indexR ArrayEltRint16   !ad !n = worker ad i n
    indexR ArrayEltRint32   !ad !n = worker ad i n
    indexR ArrayEltRint64   !ad !n = worker ad i n
    indexR ArrayEltRword    !ad !n = worker ad i n
    indexR ArrayEltRword8   !ad !n = worker ad i n
    indexR ArrayEltRword16  !ad !n = worker ad i n
    indexR ArrayEltRword32  !ad !n = worker ad i n
    indexR ArrayEltRword64  !ad !n = worker ad i n
    indexR ArrayEltRhalf    !ad !n = worker ad i n
    indexR ArrayEltRfloat   !ad !n = worker ad i n
    indexR ArrayEltRdouble  !ad !n = worker ad i n
    indexR ArrayEltRchar    !ad !n = worker ad i n
    indexR ArrayEltRbool    !ad !n = worker ad i n
    --
    indexR (ArrayEltRpair !aeR1 !aeR2) (AD_Pair !ad1 !ad2) !n = liftM2 AD_Pair (indexR aeR1 ad1 n) (indexR aeR2 ad2 n)
    indexR (ArrayEltRvec  !aeR)        (AD_Vec w# !ad)     !n = liftM (AD_Vec w#) (indexR aeR ad (I# w# * n))

{-# INLINE runIndexArrayAsync #-}
runIndexArrayAsync
    :: forall arch sh e. Async arch
    => (forall s a. (ArrayElt s, ArrayPtrs s ~ Ptr a, Storable a, Typeable a, Typeable s) => ArrayData s -> Int -> Int -> Par arch (FutureR arch (ArrayData s)))
    -> Array sh e
    -> Int
    -> Par arch (FutureR arch e)
runIndexArrayAsync worker (Array _ adata) i = (toElt . flip unsafeIndexArrayData 0) `liftF` indexR arrayElt adata 1
  where
    indexR :: ArrayEltR s -> ArrayData s -> Int -> Par arch (FutureR arch (ArrayData s))
    indexR ArrayEltRunit    !_  !_ = newFull AD_Unit
    indexR ArrayEltRint     !ad !n = worker ad i n
    indexR ArrayEltRint8    !ad !n = worker ad i n
    indexR ArrayEltRint16   !ad !n = worker ad i n
    indexR ArrayEltRint32   !ad !n = worker ad i n
    indexR ArrayEltRint64   !ad !n = worker ad i n
    indexR ArrayEltRword    !ad !n = worker ad i n
    indexR ArrayEltRword8   !ad !n = worker ad i n
    indexR ArrayEltRword16  !ad !n = worker ad i n
    indexR ArrayEltRword32  !ad !n = worker ad i n
    indexR ArrayEltRword64  !ad !n = worker ad i n
    indexR ArrayEltRhalf    !ad !n = worker ad i n
    indexR ArrayEltRfloat   !ad !n = worker ad i n
    indexR ArrayEltRdouble  !ad !n = worker ad i n
    indexR ArrayEltRchar    !ad !n = worker ad i n
    indexR ArrayEltRbool    !ad !n = worker ad i n
    --
    indexR (ArrayEltRpair !aeR1 !aeR2) (AD_Pair !ad1 !ad2) !n = liftF2' AD_Pair (indexR aeR1 ad1 n) (indexR aeR2 ad2 n)
    indexR (ArrayEltRvec  !aeR)        (AD_Vec w# !ad)     !n = liftF' (AD_Vec w#) (indexR aeR ad (I# w# * n))

    -- It is expected these transfers will be very small, so don't bother
    -- creating new execution streams for them
    liftF' :: (a -> b) -> Par arch (FutureR arch a) -> Par arch (FutureR arch b)
    liftF' f x = do
      r  <- new
      x' <- x
      put r . f =<< get x'
      return r

    liftF2' :: (a -> b -> c) -> Par arch (FutureR arch a) -> Par arch (FutureR arch b) -> Par arch (FutureR arch c)
    liftF2' f x y = do
      r  <- new
      x' <- x
      y' <- y
      put r =<< liftM2 f (get x') (get y')
      return r


-- | Generalised function to traverse the Arrays structure
--
{-# INLINE runArrays #-}
runArrays
    :: forall m arrs. (Monad m, Arrays arrs)
    => arrs
    -> (forall sh e. Array sh e -> m (Array sh e))
    -> m arrs
runArrays arrs worker = toArr `liftM` runR (arrays @arrs) (fromArr arrs)
  where
    runR :: ArraysR a -> a -> m a
    runR ArraysRunit             ()             = return ()
    runR ArraysRarray            arr            = worker arr
    runR (ArraysRpair aeR2 aeR1) (arrs2, arrs1) = liftM2 (,) (runR aeR2 arrs2) (runR aeR1 arrs1)

{-# INLINE runArraysAsync #-}
runArraysAsync
    :: forall arch arrs. (Async arch, Arrays arrs)
    => arrs
    -> (forall sh e. Array sh e -> Par arch (FutureR arch (Array sh e)))
    -> Par arch (FutureR arch arrs)
runArraysAsync arrs worker = toArr `liftF` runR (arrays @arrs) (fromArr arrs)
  where
    runR :: ArraysR a -> a -> Par arch (FutureR arch a)
    runR ArraysRunit ()                         = newFull ()
    runR ArraysRarray arr                       = worker arr
    runR (ArraysRpair aeR2 aeR1) (arrs2, arrs1) = liftF2 (,) (runR aeR2 arrs2) (runR aeR1 arrs1)


-- | Generalised function to traverse the ArrayData structure with one
-- additional argument
--
{-# INLINE runArray #-}
runArray
    :: forall m sh e. Monad m
    => Array sh e
    -> (forall e' p. (ArrayElt e', ArrayPtrs e' ~ Ptr p, Storable p, Typeable p, Typeable e') => Int -> ArrayData e' -> m (ArrayData e'))
    -> m (Array sh e)
runArray (Array sh adata) worker = Array sh `liftM` runR arrayElt adata 1
  where
    runR :: ArrayEltR e' -> ArrayData e' -> Int -> m (ArrayData e')
    runR ArrayEltRunit    !_  !_ = return AD_Unit
    runR ArrayEltRint     !ad !n = worker n ad
    runR ArrayEltRint8    !ad !n = worker n ad
    runR ArrayEltRint16   !ad !n = worker n ad
    runR ArrayEltRint32   !ad !n = worker n ad
    runR ArrayEltRint64   !ad !n = worker n ad
    runR ArrayEltRword    !ad !n = worker n ad
    runR ArrayEltRword8   !ad !n = worker n ad
    runR ArrayEltRword16  !ad !n = worker n ad
    runR ArrayEltRword32  !ad !n = worker n ad
    runR ArrayEltRword64  !ad !n = worker n ad
    runR ArrayEltRhalf    !ad !n = worker n ad
    runR ArrayEltRfloat   !ad !n = worker n ad
    runR ArrayEltRdouble  !ad !n = worker n ad
    runR ArrayEltRbool    !ad !n = worker n ad
    runR ArrayEltRchar    !ad !n = worker n ad
    --
    runR (ArrayEltRpair !aeR2 !aeR1) (AD_Pair !ad2 !ad1) !n = liftM2 AD_Pair (runR aeR2 ad2 n) (runR aeR1 ad1 n)
    runR (ArrayEltRvec  !aeR)        (AD_Vec w# !ad)     !n = liftM (AD_Vec w#) (runR aeR ad (I# w# * n))

{-# INLINE runArrayAsync #-}
runArrayAsync
    :: forall arch sh e. Async arch
    => Array sh e
    -> (forall e' p. (ArrayElt e', ArrayPtrs e' ~ Ptr p, Storable p, Typeable p, Typeable e') => Int -> ArrayData e' -> Par arch (FutureR arch (ArrayData e')))
    -> Par arch (FutureR arch (Array sh e))
runArrayAsync (Array sh adata) worker = Array sh `liftF` runR arrayElt adata 1
  where
    runR :: ArrayEltR e' -> ArrayData e' -> Int -> Par arch (FutureR arch (ArrayData e'))
    runR ArrayEltRunit    !_  !_ = newFull AD_Unit
    runR ArrayEltRint     !ad !n = worker n ad
    runR ArrayEltRint8    !ad !n = worker n ad
    runR ArrayEltRint16   !ad !n = worker n ad
    runR ArrayEltRint32   !ad !n = worker n ad
    runR ArrayEltRint64   !ad !n = worker n ad
    runR ArrayEltRword    !ad !n = worker n ad
    runR ArrayEltRword8   !ad !n = worker n ad
    runR ArrayEltRword16  !ad !n = worker n ad
    runR ArrayEltRword32  !ad !n = worker n ad
    runR ArrayEltRword64  !ad !n = worker n ad
    runR ArrayEltRhalf    !ad !n = worker n ad
    runR ArrayEltRfloat   !ad !n = worker n ad
    runR ArrayEltRdouble  !ad !n = worker n ad
    runR ArrayEltRbool    !ad !n = worker n ad
    runR ArrayEltRchar    !ad !n = worker n ad
    --
    runR (ArrayEltRpair !aeR2 !aeR1) (AD_Pair !ad2 !ad1) !n = liftF2 AD_Pair (runR aeR2 ad2 n) (runR aeR1 ad1 n)
    runR (ArrayEltRvec  !aeR)        (AD_Vec w# !ad)     !n = liftF (AD_Vec w#) (runR aeR ad (I# w# * n))


{-# INLINE liftF #-}
liftF :: Async arch
      => (a -> b)
      -> Par arch (FutureR arch a)
      -> Par arch (FutureR arch b)
liftF f x = do
  r  <- new
  x' <- x
  fork $ put r . f =<< get x'
  return r

{-# INLINE liftF2 #-}
liftF2 :: Async arch
       => (a -> b -> c)
       -> Par arch (FutureR arch a)
       -> Par arch (FutureR arch b)
       -> Par arch (FutureR arch c)
liftF2 f x y = do
  r  <- new
  x' <- spawn x
  y' <- spawn y
  fork $ put r =<< liftM2 f (get x') (get y')
  return r

