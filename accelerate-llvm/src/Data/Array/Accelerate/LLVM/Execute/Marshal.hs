{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Execute.Marshal
-- Copyright   : [2014..2018] Trevor L. McDonell
--               [2014..2014] Vinod Grover (NVIDIA Corporation)
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Execute.Marshal
  where

-- accelerate
import Data.Array.Accelerate.Array.Data
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Type

-- libraries
import Data.Proxy                                               ( Proxy )
import Data.DList                                               ( DList )
import qualified Data.DList                                     as DL


-- Marshalling arguments
-- ---------------------

-- | Convert function arguments into stream a form suitable for function calls
--
{-# INLINE marshal #-}
marshal :: Marshalable arch m args => Proxy arch -> args -> m [ArgR arch]
marshal proxy args = DL.toList `fmap` marshal' proxy args


-- | A type family that is used to specify a concrete kernel argument and
-- stream/context type for a given backend target.
--
type family ArgR arch


-- | Data which can be marshalled as function arguments to kernels.
--
-- These are just the basic definitions that don't require backend specific
-- knowledge. To complete the definition, a backend must provide instances for:
--
--   * Int                      -- for shapes
--   * ArrayData e              -- for array data
--   * (Gamma aenv, Aval aenv)  -- for free array variables
--
class Monad m => Marshalable arch m a where
  marshal' :: Proxy arch -> a -> m (DList (ArgR arch))

instance Monad m => Marshalable arch m () where
  {-# INLINE marshal' #-}
  marshal' _ () = return DL.empty

instance (Marshalable arch m a, Marshalable arch m b) => Marshalable arch m (a, b) where
  {-# INLINE marshal' #-}
  marshal' proxy (a, b) =
    DL.concat `fmap` sequence [marshal' proxy a, marshal' proxy b]

instance (Marshalable arch m a, Marshalable arch m b, Marshalable arch m c) => Marshalable arch m (a, b, c) where
  {-# INLINE marshal' #-}
  marshal' proxy (a, b, c) =
    DL.concat `fmap` sequence [marshal' proxy a, marshal' proxy b, marshal' proxy c]

instance (Marshalable arch m a, Marshalable arch m b, Marshalable arch m c, Marshalable arch m d) => Marshalable arch m (a, b, c, d) where
  {-# INLINE marshal' #-}
  marshal' proxy (a, b, c, d) =
    DL.concat `fmap` sequence [marshal' proxy a, marshal' proxy b, marshal' proxy c, marshal' proxy d]

instance (Marshalable arch m a, Marshalable arch m b, Marshalable arch m c, Marshalable arch m d, Marshalable arch m e)
    => Marshalable arch m (a, b, c, d, e) where
  {-# INLINE marshal' #-}
  marshal' proxy (a, b, c, d, e) =
    DL.concat `fmap` sequence [marshal' proxy a, marshal' proxy b, marshal' proxy c, marshal' proxy d, marshal' proxy e]

instance (Marshalable arch m a, Marshalable arch m b, Marshalable arch m c, Marshalable arch m d, Marshalable arch m e, Marshalable arch m f)
    => Marshalable arch m (a, b, c, d, e, f) where
  {-# INLINE marshal' #-}
  marshal' proxy (a, b, c, d, e, f) =
    DL.concat `fmap` sequence [marshal' proxy a, marshal' proxy b, marshal' proxy c, marshal' proxy d, marshal' proxy e, marshal' proxy f]

instance (Marshalable arch m a, Marshalable arch m b, Marshalable arch m c, Marshalable arch m d, Marshalable arch m e, Marshalable arch m f, Marshalable arch m g)
    => Marshalable arch m (a, b, c, d, e, f, g) where
  {-# INLINE marshal' #-}
  marshal' proxy (a, b, c, d, e, f, g) =
    DL.concat `fmap` sequence [marshal' proxy a, marshal' proxy b, marshal' proxy c, marshal' proxy d, marshal' proxy e, marshal' proxy f, marshal' proxy g]

instance (Marshalable arch m a, Marshalable arch m b, Marshalable arch m c, Marshalable arch m d, Marshalable arch m e, Marshalable arch m f, Marshalable arch m g, Marshalable arch m h)
    => Marshalable arch m (a, b, c, d, e, f, g, h) where
  {-# INLINE marshal' #-}
  marshal' proxy (a, b, c, d, e, f, g, h) =
    DL.concat `fmap` sequence [marshal' proxy a, marshal' proxy b, marshal' proxy c, marshal' proxy d, marshal' proxy e, marshal' proxy f, marshal' proxy g, marshal' proxy h]

instance Marshalable arch m a => Marshalable arch m [a] where
  {-# INLINE marshal' #-}
  marshal' proxy = fmap DL.concat . mapM (marshal' proxy)

-- instance Monad m => Marshalable arch m (DList (ArgR arch)) where
--   marshal' _ = return

-- instance (Async arch, Marshalable arch (Par arch) a) => Marshalable arch (Par arch) (FutureR arch a) where
--   marshal' proxy future = marshal' proxy =<< get future

instance (Shape sh, Marshalable arch m Int, Marshalable arch m (ArrayData (EltRepr e)))
    => Marshalable arch m (Array sh e) where
  {-# INLINE marshal' #-}
  marshal' proxy (Array sh adata) =
    DL.concat `fmap` sequence [marshal' proxy adata, go proxy (eltType @sh) sh]
    where
      go :: Proxy arch -> TupleType a -> a -> m (DList (ArgR arch))
      go _ TypeRunit         ()       = return DL.empty
      go p (TypeRpair ta tb) (sa, sb) = DL.concat `fmap` sequence [go p ta sa, go p tb sb]
      go p (TypeRscalar t)   i
        | SingleScalarType (NumSingleType (IntegralNumType TypeInt{})) <- t = marshal' p i
        | otherwise                                                         = $internalError "marshal" "expected Int argument"

instance {-# INCOHERENT #-} (Shape sh, Monad m, Marshalable arch m Int)
    => Marshalable arch m sh where
  {-# INLINE marshal' #-}
  marshal' proxy sh = go proxy (eltType @sh) (fromElt sh)
    where
      go :: Proxy arch -> TupleType a -> a -> m (DList (ArgR arch))
      go _ TypeRunit         ()       = return DL.empty
      go p (TypeRpair ta tb) (sa, sb) = DL.concat `fmap` sequence [go p ta sa, go p tb sb]
      go p (TypeRscalar t)   i
        | SingleScalarType (NumSingleType (IntegralNumType TypeInt{})) <- t = marshal' p i
        | otherwise                                                         = $internalError "marshal" "expected Int argument"

-- instance Monad m => Marshalable arch m Z where
--   marshal' _ Z = return DL.empty

-- instance (Shape sh, Marshalable arch m sh, Marshalable arch m Int)
--     => Marshalable arch m (sh :. Int) where
--   marshal' proxy (sh :. sz) =
--     DL.concat `fmap` sequence [marshal' proxy sh, marshal' proxy sz]

-- instance Marshalable arch (Gamma aenv, ValR arch aenv) where
--   marshal' (gamma, aenv)
--     = fmap DL.concat
--     $ mapM (\(_, Idx' idx) -> marshal' =<< get (prj idx aenv)) (IM.elems gamma)

