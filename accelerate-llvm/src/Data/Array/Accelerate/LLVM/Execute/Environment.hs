{-# LANGUAGE CPP                 #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeFamilies        #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Execute.Environment
-- Copyright   : [2014..2018] Trevor L. McDonell
--               [2014..2014] Vinod Grover (NVIDIA Corporation)
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Execute.Environment
  where

-- accelerate
import Data.Array.Accelerate.Array.Sugar                            ( ArraysR(..) )
import Data.Array.Accelerate.AST                                    ( Idx(..) )
#if __GLASGOW_HASKELL__ < 800
import Data.Array.Accelerate.Error
#endif

import Data.Array.Accelerate.LLVM.Execute.Async
import Data.Array.Accelerate.LLVM.CodeGen.Environment               ( Idx'(..) )
import qualified Data.Array.Accelerate.LLVM.CodeGen.Environment     as CodeGen

import Control.Monad                                                ( foldM )
import qualified Data.IntMap                                        as IM


-- Environments
-- ------------

-- Valuation for an environment of futures
--
data ValR arch env where
  Empty :: ValR arch ()
  Push  :: ValR arch env -> FutureR arch t -> ValR arch (env, t)


-- Projection of a value from a valuation using a de Bruijn index.
--
{-# INLINEABLE prj #-}
prj :: Idx env t -> ValR arch env -> FutureR arch t
prj ZeroIdx       (Push _   x) = x
prj (SuccIdx idx) (Push val _) = prj idx val
#if __GLASGOW_HASKELL__ < 800
prj _             _            = $internalError "prj" "inconsistent valuation"
#endif


-- Free array variables used by a computation.
--
-- These will be marshalled to the generated function, and thus must match the
-- order as defined by code generation.
--
data Gamma aenv where
  Gamma :: ArraysR arrs -> arrs -> Gamma aenv

-- Extract the free arrays from the environment
--
{-# INLINEABLE makeGamma #-}
makeGamma :: forall arch aenv. Async arch => CodeGen.Gamma aenv -> ValR arch aenv -> Par arch (Gamma aenv)
makeGamma im aenv =
  let
      go :: Gamma aenv -> Idx' aenv -> Par arch (Gamma aenv)
      go (Gamma aeR as) (Idx' idx) = do
        a     <- get (prj idx aenv)
        return $ Gamma (ArraysRpair aeR ArraysRarray) (as, a)
  in
  foldM go (Gamma ArraysRunit ()) [ ix | (_, ix) <- IM.elems im ]

