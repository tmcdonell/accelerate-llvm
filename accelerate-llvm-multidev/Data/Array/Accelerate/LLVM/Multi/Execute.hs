{-# LANGUAGE CPP              #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE RecordWildCards  #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# OPTIONS -fno-warn-orphans #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Multi.Execute
-- Copyright   : [2014..2015] Trevor L. McDonell
--               [2014..2014] Vinod Grover (NVIDIA Corporation)
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Multi.Execute (

  executeAcc, executeAfun1,

) where

-- accelerate
import Data.Array.Accelerate.Array.Sugar                        ( Array(..), Shape, Elt, size )
import Data.Array.Accelerate.Error                              ( internalError )

import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.Execute
import Data.Array.Accelerate.LLVM.Execute.Marshal
import Data.Array.Accelerate.LLVM.Execute.Environment           ( AvalR(..) )

import Data.Array.Accelerate.LLVM.Multi.Array.Data
import Data.Array.Accelerate.LLVM.Multi.Async
import Data.Array.Accelerate.LLVM.Multi.Compile
import Data.Array.Accelerate.LLVM.Multi.Execute.Environment
import Data.Array.Accelerate.LLVM.Multi.Target

import Data.Range.Range                                         ( Range(..), trisect )
import Control.Parallel.Meta
import Control.Parallel.Meta.Worker

import Data.Array.Accelerate.Debug

-- accelerate-llvm
import Data.Array.Accelerate.LLVM.PTX.Internal                  ( PTX, Kernel )
import Data.Array.Accelerate.LLVM.Native.Internal               ( Native )
import qualified Data.Array.Accelerate.LLVM.PTX.Internal        as PTX
import qualified Data.Array.Accelerate.LLVM.Native.Internal     as CPU

-- standard library
import Prelude                                                  hiding ( map, mapM_, scanl, scanr )
import Control.Monad                                            ( void )
import Control.Monad.State                                      ( gets, liftIO )
import Data.Int
import Text.Printf


instance Execute Multi where
  map           = simpleOp
  generate      = simpleOp
  transform     = simpleOp
  backpermute   = simpleOp


-- Cooperatively run the default executable for each of the backends
--
simpleOp
    :: (Shape sh, Elt e)
    => ExecutableR Multi
    -> Gamma aenv
    -> Aval aenv
    -> Stream
    -> sh
    -> LLVM Multi (Array sh e)
simpleOp MultiR{..} gamma aenv stream sh = do
  let
      ptx1 = case ptxKernel ptxExecutable1 of
               k:_ -> k
               _   -> $internalError "execute" "kernel not found"

      ptx2 = case ptxKernel ptxExecutable2 of
               k:_ -> k
               _   -> $internalError "execute" "kernel not found"
  --
  out   <- allocateRemote sh
  multi <- gets llvmTarget
  liftIO $ executeOp multi nativeExecutable ptx1 ptx2 gamma aenv stream (size sh) out out
  return out


executeOp
    :: (Marshalable Native args, Marshalable PTX args)
    => Multi
    -> ExecutableR Native
    -> Kernel
    -> Kernel
    -> Gamma aenv
    -> Aval aenv
    -> Stream
    -> Int
    -> args
    -> Array sh e
    -> IO ()
executeOp Multi{..} cpu ptx1 ptx2 gamma aval (s1,s2) n args result@Array{} = do
  let -- Initialise each backend with an equal portion of work
      (u,v,w)      = trisect (IE 0 n)

      using  = flip PTX.evalPTX
      cpuPPT = 5000
      ptxPPT = 500000

      goCPU =
        CPU.executeMain (executableR cpu)                              $ \f              -> do
        runExecutable (CPU.fillP nativeTarget) cpuPPT u mempty Nothing $ \start end _tid -> do
          f =<< marshal nativeTarget () (start, end, args, (gamma, avalForCPU aval))
          traceIO dump_sched (printf "CPU did range [%d,%d]" start end)

      goPTX1 =
        runExecutable (PTX.fillP ptxTarget1)   ptxPPT v mempty Nothing $ \start end _tid -> do
          PTX.launch ptx1 s1 (end-start) =<< marshal ptxTarget1 s1 (i32 start, i32 end, args, (gamma, avalForPTX (\(AsyncR e a) -> AsyncR (fst e) a) aval))
          runArray result (copyToHostR start end (Just s1)) `using` ptxTarget1
          traceIO dump_sched (printf "PTX-1 did range [%d,%d]" start end)

      goPTX2 =
          runExecutable (PTX.fillP ptxTarget2) ptxPPT w mempty Nothing $ \start end _tid -> do
            PTX.launch ptx2 s2 (end-start) =<< marshal ptxTarget2 s2 (i32 start, i32 end, args, (gamma, avalForPTX (\(AsyncR e a) -> AsyncR (snd e) a) aval))
            runArray result (copyToHostR start end (Just s2)) `using` ptxTarget2
            traceIO dump_sched (printf "PTX-2 did range [%d,%d]" start end)

      i32 :: Int -> Int32
      i32 = fromIntegral

  -- Kick off the workers
  liftIO . gangIO monitorGang $ \thread ->
    case thread of
      0 -> goCPU  >> traceIO dump_sched "sched/multi: Native exiting"
      1 -> goPTX1 >> traceIO dump_sched "sched/multi: PTX-1 exiting"
      2 -> goPTX2 >> traceIO dump_sched "sched/multi: PTX-2 exiting"
      _ -> return ()

  -- Distribute the completed result to the GPUs
  liftIO . gangIO (CPU.theGang nativeTarget) $ \thread ->
    case thread of
      0 -> void $ copyToRemoteAsync s1 result `using` ptxTarget1
      1 -> void $ copyToRemoteAsync s2 result `using` ptxTarget2
      _ -> return ()


-- syncWith :: (Int -> Int -> IO ()) -> Finalise
-- syncWith copy = Finalise $ \_ -> mapM_ (\(IE from to) -> copy from to)

-- Busywork to convert the array environment into a representation specific to
-- each backend.
--
avalForCPU :: Aval aenv -> AvalR Native aenv
avalForCPU Aempty                    = Aempty
avalForCPU (Apush aenv (AsyncR _ a)) = avalForCPU aenv `Apush` AsyncR () a

avalForPTX :: (forall a. AsyncR Multi a -> AsyncR PTX a) -> Aval aenv -> AvalR PTX aenv
avalForPTX _ Aempty         = Aempty
avalForPTX f (Apush aenv a) = avalForPTX f aenv `Apush` f a

