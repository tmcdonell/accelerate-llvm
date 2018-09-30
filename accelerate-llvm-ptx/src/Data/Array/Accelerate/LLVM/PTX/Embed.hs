{-# LANGUAGE CPP             #-}
{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.Embed
-- Copyright   : [2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.Embed (

  module Data.Array.Accelerate.LLVM.Embed,

) where

import Data.ByteString.Short.Extra                                  as BS

import Data.Array.Accelerate.Lifetime

import Data.Array.Accelerate.LLVM.Compile
import Data.Array.Accelerate.LLVM.Embed
import Data.Array.Accelerate.LLVM.Embed.Environment
import Data.Array.Accelerate.LLVM.Embed.Extra

import Data.Array.Accelerate.LLVM.PTX.Compile
import Data.Array.Accelerate.LLVM.PTX.Context
import Data.Array.Accelerate.LLVM.PTX.Execute                       ( )
import Data.Array.Accelerate.LLVM.PTX.Execute.Async
import Data.Array.Accelerate.LLVM.PTX.Link
import Data.Array.Accelerate.LLVM.PTX.Target

import qualified Foreign.CUDA.Driver                                as CUDA

import Data.Typeable
import Foreign.Ptr
import GHC.Ptr                                                      ( Ptr(..) )
import Language.Haskell.TH                                          ( Q, TExp )
import System.IO.Unsafe
import qualified Data.ByteString                                    as B
import qualified Data.ByteString.Unsafe                             as B
import qualified Language.Haskell.TH                                as TH
import qualified Language.Haskell.TH.Syntax                         as TH


{-# SPECIALISE INLINE embedOpenAcc :: (Typeable aenv, Typeable arrs) => PTX -> CompiledOpenAcc PTX aenv arrs -> AvalQ PTX aenv -> TExpQ (Par PTX (Future arrs)) #-}

instance Embed PTX where
  embedForTarget = embed

-- Embed the given object code and set up to be reloaded at execution time.
--
embed :: PTX -> ObjectR PTX -> Q (TExp (ExecutableR PTX))
embed target (ObjectR _ cfg obj) = do
  -- Load the module to recover information such as number of registers and
  -- bytes of shared memory. It may be possible to do this without requiring an
  -- active CUDA context.
  kmd <- TH.runIO $ withContext (ptxContext target) $ do
            jit <- B.unsafeUseAsCString obj $ \p -> CUDA.loadDataFromPtrEx (castPtr p) []
            ks  <- mapM (uncurry (linkFunctionQ (CUDA.jitModule jit))) cfg
            CUDA.unload (CUDA.jitModule jit)
            return ks

  -- Generate the embedded kernel executable. This will load the embedded object
  -- code into the current (at execution time) context.
  --
  -- TLM 2018-09-08: It might be nice to lift this to a top-level declaration,
  -- but we can't be sure that it will always be executed using the same device
  -- context (runQWith), so just leave it inline with the generated code.
  -- I guess we should also check that GHC doesn't lift this out into
  -- a top-level CAF.
  --
  [|| unsafePerformIO $ do
        jit <- CUDA.loadDataFromPtrEx $$( TH.unsafeTExpCoerce [| Ptr $(TH.litE (TH.StringPrimL (B.unpack obj))) |] ) []
        fun <- newLifetime (FunctionTable $$(listE (map (linkQ 'jit) kmd)))
        return $ PTXR fun
   ||]
  where
    linkQ :: TH.Name -> (Kernel, Q (TExp (Int -> Int))) -> Q (TExp Kernel)
    linkQ jit (Kernel name _ dsmem cta _, grid) =
      [|| unsafePerformIO $ do
#if MIN_VERSION_cuda(0,10,0)
            f <- CUDA.getFun (CUDA.jitModule $$(TH.unsafeTExpCoerce (TH.varE jit))) $$(liftSBS name)
#else
            f <- CUDA.getFun (CUDA.jitModule $$(TH.unsafeTExpCoerce (TH.varE jit))) $$(TH.unsafeTExpCoerce (TH.lift (S8.unpack name)))
#endif
            return $ Kernel $$(liftSBS name) f dsmem cta $$grid
       ||]

    listE :: [Q (TExp a)] -> Q (TExp [a])
    listE xs = TH.unsafeTExpCoerce (TH.listE (map TH.unTypeQ xs))

