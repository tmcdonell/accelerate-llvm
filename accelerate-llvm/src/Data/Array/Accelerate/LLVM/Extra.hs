{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Extra
-- Copyright   : [2014..2017] Trevor L. McDonell
--               [2014..2014] Vinod Grover (NVIDIA Corporation)
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Extra
  where

-- accelerate
import Data.Array.Accelerate.Error

-- standard library
import Data.Word
import qualified Data.Bits                                          as B


-- | The number of bits in a type
--
{-# INLINE bitSize #-}
bitSize :: B.Bits a => a -> Word32
bitSize x
  | Just s <- B.bitSizeMaybe x  = fromIntegral s
  | otherwise                   = $internalError "bitSize" "could not determine bit size of type"


-- | Convert a boolean value into an integral value, where False is zero and
-- True is one.
--
{-# INLINE fromBool #-}
fromBool :: Integral i => Bool -> i
fromBool True  = 1
fromBool False = 0

-- | Convert an integral value into a boolean. We follow the C convention, where
-- zero is False and all other values represent True.
--
{-# INLINE toBool #-}
toBool :: Integral i => i -> Bool
toBool 0 = False
toBool _ = True


{-# INLINE ($$) #-}
infixr 0 $$
($$) :: (a -> b) -> (c -> d -> a) -> c -> d -> b
(f $$ g) x y = f (g x y)

{-# INLINE ($$$) #-}
infixr 0 $$$
($$$) :: (a -> b) -> (c -> d -> e -> a) -> c -> d -> e -> b
(f $$$ g) x y z = f (g x y z)

{-# INLINE ($$$$) #-}
infixr 0 $$$$
($$$$) :: (a -> b) -> (c -> d -> e -> f -> a) -> c -> d -> e -> f -> b
(f $$$$ g) x y z w = f (g x y z w)

