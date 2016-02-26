{-# LANGUAGE CPP             #-}
{-# LANGUAGE TemplateHaskell #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Multi.State
-- Copyright   : [2014..2015] Trevor L. McDonell
--               [2014..2014] Vinod Grover (NVIDIA Corporation)
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Multi.State (

  evalMulti,
  createTarget, defaultTarget

) where

-- accelerate
import Data.Array.Accelerate.Error

import Control.Parallel.Meta
import Control.Parallel.Meta.Worker
import qualified Control.Parallel.Meta.Trans.LBS                as LBS
import qualified Control.Parallel.Meta.Resource.SMP             as SMP
import qualified Control.Parallel.Meta.Resource.Single          as Single

import Data.Array.Accelerate.LLVM.State
import Data.Array.Accelerate.LLVM.Multi.Target
import Data.Array.Accelerate.LLVM.PTX.Internal                  ( PTX )
import Data.Array.Accelerate.LLVM.Native.Internal               ( Native )
import qualified Data.Array.Accelerate.LLVM.PTX.Internal        as PTX
import qualified Data.Array.Accelerate.LLVM.Native.Internal     as CPU

import qualified Data.Array.Accelerate.Debug                    as Debug

-- cuda
import Foreign.CUDA.Driver.Error
import qualified Foreign.CUDA.Driver                            as CUDA

-- standard library
import Data.Monoid
import Control.Exception                                        ( bracket_, catch )
import Control.Concurrent                                       ( runInBoundThread )
import System.IO.Unsafe                                         ( unsafePerformIO )
import Prelude                                                  hiding ( init )

import GHC.Conc


-- | Execute a computation in the Multi backend. Requires initialising the CUDA
-- environment; copied from that backend.
--
evalMulti :: Multi -> LLVM Multi a -> IO a
evalMulti multi acc =
  runInBoundThread (bracket_ setup teardown action)
  `catch`
  \e -> $internalError "unhandled" (show (e :: CUDAException))
  where
    setup       = PTX.push (PTX.ptxContext (ptxTarget1 multi)) >>
                  PTX.push (PTX.ptxContext (ptxTarget2 multi))
    teardown    = PTX.pop >> PTX.pop
    action      = evalLLVM multi acc


-- | Create a multi-device execution target by combining the given CPU and GPU
-- targets.
--
-- This spawns a thread to control each execution unit. A lazy binary splitting
-- work-stealing scheduler is used to balance the load amongst the available
-- processors. A suitable PPT should be chosen when invoking the continuation in
-- order to balance scheduler overhead with fine-grained function calls.
--
createTarget :: Native -> PTX -> PTX -> IO Multi
createTarget native ptx1 ptx2 = do

  -- We still need to spawn a monitor thread for each GPU so that it can
  -- participate in work stealing.
  gpuGang1 <- forkGang 1
  gpuGang2 <- forkGang 1
  cpuGang  <- return (CPU.theGang native)

  gangIO gpuGang1 $ \_ -> PTX.push (PTX.ptxContext ptx1) >> PTX.push (PTX.ptxContext ptx2)
  gangIO gpuGang2 $ \_ -> PTX.push (PTX.ptxContext ptx1) >> PTX.push (PTX.ptxContext ptx2)
  gangIO cpuGang  $ \_ -> PTX.push (PTX.ptxContext ptx1) >> PTX.push (PTX.ptxContext ptx2)

  let
      -- The basic resources for the CPU and GPU. As we don't currently support
      -- multiple GPUs, the lone GPU knows of no other sources of work.
      --
      gpuR1     = Single.mkResource
      gpuR2     = Single.mkResource
      cpuR      = SMP.mkResource (2 * gangSize cpuGang) cpuGang

      -- Construct the new Executable contexts for each backend, where the CPU
      -- can steal from the GPU, and vice-versa.
      --
      -- Note that each backend does not need to know about the PPT for the
      -- other: individual backends only need to know the best way to split the
      -- data for themselves (to balance the frequency of deque checks to doing
      -- useful work, or rather, how expensive it is to jump out of the
      -- execution function and back to the scheduler). When work is stolen from
      -- another processor, they steal the whole chunk, and then subdivide it
      -- based on their own PPT.
      --
      native'   = native { CPU.fillP = Executable $ \ppt range sync init fill ->
                              parIO (LBS.mkResource ppt cpuR <> gpuR1 <> gpuR2) cpuGang range init fill sync }

      ptx1'     = ptx1   { PTX.fillP = Executable $ \ppt range sync init fill ->
                              parIO (LBS.mkResource ppt gpuR1 <> gpuR2 <> cpuR) gpuGang1 range init fill sync }

      ptx2'     = ptx2   { PTX.fillP = Executable $ \ppt range sync init fill ->
                              parIO (LBS.mkResource ppt gpuR2 <> gpuR1 <> cpuR) gpuGang2 range init fill sync }
  --
  return $! Multi ptx1' ptx2' native' defaultMonitor


-- Top-level mutable state
-- -----------------------
--
-- It is important to keep some information alive for the entire run of the
-- program, not just a single execution. These tokens use 'unsafePerformIO' to
-- ensure they are executed only once, and reused for subsequent invocations.
--

-- | Initialise the CPU threads and GPUs that will be used to execute
-- computations. This spawns one worker on each capability, which can be set via
-- +RTS -Nn. Note that the GPU worker(s) constitute one capability, so for N CPU
-- worker threads, you must specify (N+1) HECs.
--
-- This globally shared target is auto-initialised on startup and used by
-- default for all computations.
--
{-# NOINLINE defaultTarget #-}
defaultTarget :: Multi
defaultTarget = unsafePerformIO $ do
  Debug.traceIO Debug.dump_gc "gc: initialise default multi target"
  CUDA.initialise []
  ngpu <- CUDA.count
  dev0 <- CUDA.device 0
  dev1 <- CUDA.device (1 `mod` ngpu)
  prp0 <- CUDA.props dev0
  prp1 <- CUDA.props dev1
  ptx0 <- PTX.createTargetForDevice dev0 prp0 []
  ptx1 <- PTX.createTargetForDevice dev1 prp1 []
  cpu  <- CPU.createTarget [1 .. ((numCapabilities-1) `max` 1)]
  createTarget cpu ptx0 ptx1

  -- createTarget CPU.defaultTarget PTX.defaultTarget

-- A gang whose only job is to dispatch the initial work distribution to the
-- available worker backends.
--
{-# NOINLINE defaultMonitor #-}
defaultMonitor :: Gang
defaultMonitor = unsafePerformIO $ forkGang 3

