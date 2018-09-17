{-# LANGUAGE BangPatterns    #-}
{-# LANGUAGE CPP             #-}
{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns    #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Native.Embed
-- Copyright   : [2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Native.Embed (

  module Data.Array.Accelerate.LLVM.Embed,

) where

import Data.ByteString.Short.Char8                                  as S8
import Data.ByteString.Short.Extra                                  as BS
import Data.ByteString.Short.Internal                               as BS

import Data.Array.Accelerate.Lifetime

import Data.Array.Accelerate.LLVM.Compile
import Data.Array.Accelerate.LLVM.Embed
import Data.Array.Accelerate.LLVM.Embed.Environment
import Data.Array.Accelerate.LLVM.Embed.Extra

import Data.Array.Accelerate.LLVM.Native.Array.Data                 ( )
import Data.Array.Accelerate.LLVM.Native.Compile
import Data.Array.Accelerate.LLVM.Native.Compile.Cache
import Data.Array.Accelerate.LLVM.Native.Execute                    ( )
import Data.Array.Accelerate.LLVM.Native.Execute.Async
import Data.Array.Accelerate.LLVM.Native.Execute.Environment
import Data.Array.Accelerate.LLVM.Native.Link
import Data.Array.Accelerate.LLVM.Native.Plugin.Annotation
import Data.Array.Accelerate.LLVM.Native.State
import Data.Array.Accelerate.LLVM.Native.Target

import Control.Concurrent.Unique
import Control.Monad
import Data.Hashable
import Data.Typeable
import Foreign.Ptr
import GHC.Ptr                                                      ( Ptr(..) )
import Language.Haskell.TH                                          ( Q, TExp )
import Numeric
import System.IO.Unsafe
import qualified Language.Haskell.TH                                as TH
import qualified Language.Haskell.TH.Syntax                         as TH


{-# SPECIALISE INLINE embedOpenAcc :: (Typeable aenv, Typeable arrs) => Native -> CompiledOpenAcc Native aenv arrs -> AvalQ Native aenv -> TExpQ (Val aenv) -> TExpQ (Par Native (Future arrs)) #-}

instance Embed Native where
  embedForTarget = embed

-- Add the given object code to the set of files to link the executable with,
-- and generate FFI declarations to access the external functions of that file.
-- The returned ExecutableR references the new FFI declarations.
--
embed :: Native -> ObjectR Native -> Q (TExp (ExecutableR Native))
embed target (ObjectR uid nms !_) = do
  objFile <- TH.runIO (evalNative target (cacheOfUID uid))
  exe     <- makeEXE objFile
  return exe
  where
    listE :: [Q (TExp a)] -> Q (TExp [a])
    listE xs = TH.unsafeTExpCoerce (TH.listE (map TH.unTypeQ xs))

    liftSBS :: ShortByteString -> Q (TExp ShortByteString)
    liftSBS bs =
      let bytes = BS.unpack bs
          len   = BS.length bs
      in
      [|| unsafePerformIO $ BS.createFromPtr $$( TH.unsafeTExpCoerce [| Ptr $(TH.litE (TH.StringPrimL bytes)) |]) len ||]

    makeEXE :: FilePath -> Q (TExp (ExecutableR Native))
    makeEXE objFile = do
      i   <- TH.runIO newUnique
      n   <- TH.newName ("__" ++ shows uid "_" ++ showHex (hash i) [])
      tab <- forM nms $ \fn -> return [|| ( $$(liftSBS (BS.take (BS.length fn - 65) fn)), $$(makeFFI fn objFile) ) ||]
      sig <- TH.sigD n [t| ExecutableR Native |]
      dec <- TH.funD n [ TH.clause [] (TH.normalB (TH.unTypeQ [|| unsafePerformIO $ NativeR `fmap` newLifetime (FunctionTable $$(listE tab)) ||])) [] ]
      TH.addTopDecls [dec, sig]
#if __GLASGOW_HASKELL__ >= 806
      TH.addForeignFilePath TH.RawObject objFile
#endif
      TH.unsafeTExpCoerce (TH.varE n)

    makeFFI :: ShortByteString -> FilePath -> Q (TExp (FunPtr ()))
    makeFFI (S8.unpack -> fn) objFile = do
      i   <- TH.runIO newUnique
      fn' <- TH.newName ("__accelerate_llvm_native_" ++ showHex (hash i) [])
      dec <- TH.forImpD TH.CCall TH.Unsafe ('&':fn) fn' [t| FunPtr () |]
      ann <- TH.pragAnnD (TH.ValueAnnotation fn') [| (Object objFile) |]
      TH.addTopDecls [dec, ann]
      TH.unsafeTExpCoerce (TH.varE fn')

