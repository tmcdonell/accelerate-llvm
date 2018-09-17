{-# LANGUAGE CPP             #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Embed.Environment
-- Copyright   : [2014..2018] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Embed.Environment
  where

import Data.Array.Accelerate.AST                                ( Idx(..) )

import Data.Array.Accelerate.LLVM.Embed.Extra
import Data.Array.Accelerate.LLVM.Execute.Async


data ValQ arch env where
  EmptyQ ::                             ValQ arch ()
  PushQ  :: ValQ arch env -> TExpQ t -> ValQ arch (env, t)

prjQ :: Idx env t -> ValQ arch env -> TExpQ t
prjQ ZeroIdx      (PushQ _   v) = v
prjQ (SuccIdx ix) (PushQ env _) = prjQ ix env
#if __GLASGOW_HASKELL__ < 800
prjQ _            _             = $internalError "prj" "inconsistent valuation"
#endif


data AvalQ arch aenv where
  AemptyQ ::                                              AvalQ arch ()
  ApushQ  :: AvalQ arch aenv -> TExpQ (FutureR arch t) -> AvalQ arch (aenv, t)

{-# INLINEABLE aprjQ #-}
aprjQ :: Idx aenv t -> AvalQ arch aenv -> TExpQ (FutureR arch t)
aprjQ ZeroIdx      (ApushQ _   v) = v
aprjQ (SuccIdx ix) (ApushQ env _) = aprjQ ix env
#if __GLASGOW_HASKELL__ < 800
aprjQ _            _              = $internalError "prj" "inconsistent valuation"
#endif

