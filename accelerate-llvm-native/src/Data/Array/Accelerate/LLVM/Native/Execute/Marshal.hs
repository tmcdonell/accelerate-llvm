{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE CPP                   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances  #-}
{-# OPTIONS_GHC -fno-warn-unrecognised-pragmas #-}
#endif
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.Execute.Marshal
-- Copyright   : [2014..2018] Trevor L. McDonell
--               [2014..2014] Vinod Grover (NVIDIA Corporation)
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.Execute.Marshal (

  Marshalable,
  M.marshal', M.marshal,

) where

-- accelerate
import Data.Array.Accelerate.LLVM.Native.Array.Data
import Data.Array.Accelerate.LLVM.Native.Execute.Async
import Data.Array.Accelerate.LLVM.Native.Target
import Data.Array.Accelerate.LLVM.State
import qualified Data.Array.Accelerate.LLVM.Execute.Marshal     as M

-- libraries
import Data.Proxy
import Data.DList                                               ( DList )
import qualified Data.DList                                     as DL
import qualified Foreign.LibFFI                                 as FFI


-- Instances for handling concrete types in the Native backend
--
type Marshalable m args     = M.Marshalable Native m args
type instance M.ArgR Native = FFI.Arg


instance Monad m => M.Marshalable Native m (DList FFI.Arg) where
  {-# INLINE marshal' #-}
  marshal' _ = return

instance Monad m => M.Marshalable Native m Int where
  {-# INLINE marshal' #-}
  marshal' _ x = return $ DL.singleton (FFI.argInt x)

instance ArrayElt e => M.Marshalable Native (Par Native) (ArrayData e) where
  {-# INLINE marshal' #-}
  marshal' arch adata = liftPar (M.marshal' arch adata)

instance ArrayElt e => M.Marshalable Native (LLVM Native) (ArrayData e) where
  {-# INLINE marshal' #-}
  marshal' arch adata = M.marshal1' arch (Proxy::Proxy ArrayElt) adata

instance M.Marshalable1 Native (Par Native) ArrayElt GArrayData where
  {-# INLINE marshal1' #-}
  marshal1' arch aer adata = liftPar (M.marshal1' arch aer adata)

instance M.Marshalable1 Native (LLVM Native) ArrayElt GArrayData where
  {-# INLINE marshal1' #-}
  marshal1' _ _ adata = return $ marshalR arrayElt adata
    where
      marshalR :: ArrayEltR e' -> ArrayData e' -> DList FFI.Arg
      marshalR ArrayEltRunit    !_  = DL.empty
      marshalR ArrayEltRint     !ad = DL.singleton $ FFI.argPtr (ptrsOfArrayData ad)
      marshalR ArrayEltRint8    !ad = DL.singleton $ FFI.argPtr (ptrsOfArrayData ad)
      marshalR ArrayEltRint16   !ad = DL.singleton $ FFI.argPtr (ptrsOfArrayData ad)
      marshalR ArrayEltRint32   !ad = DL.singleton $ FFI.argPtr (ptrsOfArrayData ad)
      marshalR ArrayEltRint64   !ad = DL.singleton $ FFI.argPtr (ptrsOfArrayData ad)
      marshalR ArrayEltRword    !ad = DL.singleton $ FFI.argPtr (ptrsOfArrayData ad)
      marshalR ArrayEltRword8   !ad = DL.singleton $ FFI.argPtr (ptrsOfArrayData ad)
      marshalR ArrayEltRword16  !ad = DL.singleton $ FFI.argPtr (ptrsOfArrayData ad)
      marshalR ArrayEltRword32  !ad = DL.singleton $ FFI.argPtr (ptrsOfArrayData ad)
      marshalR ArrayEltRword64  !ad = DL.singleton $ FFI.argPtr (ptrsOfArrayData ad)
      marshalR ArrayEltRhalf    !ad = DL.singleton $ FFI.argPtr (ptrsOfArrayData ad)
      marshalR ArrayEltRfloat   !ad = DL.singleton $ FFI.argPtr (ptrsOfArrayData ad)
      marshalR ArrayEltRdouble  !ad = DL.singleton $ FFI.argPtr (ptrsOfArrayData ad)
      marshalR ArrayEltRchar    !ad = DL.singleton $ FFI.argPtr (ptrsOfArrayData ad)
      marshalR ArrayEltRbool    !ad = DL.singleton $ FFI.argPtr (ptrsOfArrayData ad)
      --
      marshalR (ArrayEltRvec  !ae)         (AD_Vec _ !ad)      = marshalR ae ad
      marshalR (ArrayEltRpair !aeR1 !aeR2) (AD_Pair !ad1 !ad2) = marshalR aeR1 ad1 `DL.append` marshalR aeR2 ad2

