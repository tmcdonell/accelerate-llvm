{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE ViewPatterns        #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.PTX.CodeGen.Base
-- Copyright   : [2014..2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.PTX.CodeGen.Base (

  -- Types
  DeviceProperties, KernelMetadata(..),

  -- Thread identifiers
  warpSize,
  blockDim_x,  blockDim_y,  blockDim_z,
  gridDim_x,   gridDim_y,   gridDim_z,
  threadIdx_x, threadIdx_y, threadIdx_z,
  blockIdx_x,  blockIdx_y,  blockIdx_z,

  gridSize_x, gridSize_y, gridSize_z,
  globalThreadIdx_x, globalThreadIdx_y, globalThreadIdx_z,

  -- Other intrinsics
  laneId, warpId,
  laneMask_eq, laneMask_lt, laneMask_le, laneMask_gt, laneMask_ge,
  atomicAdd_f,

  -- Barriers and synchronisation
  __syncthreads,
  __threadfence_block, __threadfence_grid,

  -- Shared memory
  staticSharedMem,
  dynamicSharedMem,
  sharedMemAddrSpace,

  -- Kernel definitions
  (+++),
  gangParam, gangParamFromTo,
  makeOpenAcc, makeOpenAccWith,

  -- miscellaneous
  module Data.Proxy,

) where

-- llvm
import LLVM.AST.Type.AddrSpace
import LLVM.AST.Type.Constant
import LLVM.AST.Type.Downcast
import LLVM.AST.Type.Global
import LLVM.AST.Type.Instruction
import LLVM.AST.Type.Instruction.Volatile
import LLVM.AST.Type.Metadata
import LLVM.AST.Type.Name
import LLVM.AST.Type.Operand
import LLVM.AST.Type.Representation
import qualified LLVM.AST.Constant                                  as LLVM hiding ( type' )
import qualified LLVM.AST.Global                                    as LLVM
import qualified LLVM.AST.Linkage                                   as LLVM
import qualified LLVM.AST.Name                                      as LLVM
import qualified LLVM.AST.Type                                      as LLVM

-- accelerate
import Data.Array.Accelerate.Analysis.Type
import Data.Array.Accelerate.Array.Sugar                            ( Shape, Elt, Vector, eltType )
import Data.Array.Accelerate.Error

import Data.Array.Accelerate.LLVM.CodeGen.Arithmetic                as A
import Data.Array.Accelerate.LLVM.CodeGen.Base
import Data.Array.Accelerate.LLVM.CodeGen.Constant
import Data.Array.Accelerate.LLVM.CodeGen.IR
import Data.Array.Accelerate.LLVM.CodeGen.Module
import Data.Array.Accelerate.LLVM.CodeGen.Monad
import Data.Array.Accelerate.LLVM.CodeGen.Ptr
import Data.Array.Accelerate.LLVM.CodeGen.Sugar

import Data.Array.Accelerate.LLVM.PTX.Analysis.Launch
import Data.Array.Accelerate.LLVM.PTX.Context
import Data.Array.Accelerate.LLVM.PTX.Target

import qualified Foreign.CUDA.Analysis                              as CUDA

-- standard library
import Control.Applicative
import Control.Monad                                                ( void )
import Data.Proxy
import Data.String
import Text.Printf
import Prelude                                                      as P


-- Thread identifiers
-- ------------------

-- | Read the builtin registers that store CUDA thread and grid identifiers
--
-- <https://github.com/llvm-mirror/llvm/blob/master/include/llvm/IR/IntrinsicsNVVM.td>
--
special_ptx_reg :: Label -> CodeGen (IR Int32)
special_ptx_reg f =
  call (Body type' f) [NoUnwind, ReadNone]

warpSize :: CodeGen (IR Int32)
warpSize    = special_ptx_reg "llvm.nvvm.read.ptx.sreg.warpsize"

laneId :: CodeGen (IR Int32)
laneId      = special_ptx_reg "llvm.nvvm.read.ptx.sreg.laneid"

blockDim_x, blockDim_y, blockDim_z :: CodeGen (IR Int32)
blockDim_x  = special_ptx_reg "llvm.nvvm.read.ptx.sreg.ntid.x"
blockDim_y  = special_ptx_reg "llvm.nvvm.read.ptx.sreg.ntid.y"
blockDim_z  = special_ptx_reg "llvm.nvvm.read.ptx.sreg.ntid.z"

gridDim_x, gridDim_y, gridDim_z :: CodeGen (IR Int32)
gridDim_x   = special_ptx_reg "llvm.nvvm.read.ptx.sreg.nctaid.x"
gridDim_y   = special_ptx_reg "llvm.nvvm.read.ptx.sreg.nctaid.y"
gridDim_z   = special_ptx_reg "llvm.nvvm.read.ptx.sreg.nctaid.z"

threadIdx_x, threadIdx_y, threadIdx_z :: CodeGen (IR Int32)
threadIdx_x = special_ptx_reg "llvm.nvvm.read.ptx.sreg.tid.x"
threadIdx_y = special_ptx_reg "llvm.nvvm.read.ptx.sreg.tid.y"
threadIdx_z = special_ptx_reg "llvm.nvvm.read.ptx.sreg.tid.z"

blockIdx_x, blockIdx_y, blockIdx_z :: CodeGen (IR Int32)
blockIdx_x  = special_ptx_reg "llvm.nvvm.read.ptx.sreg.ctaid.x"
blockIdx_y  = special_ptx_reg "llvm.nvvm.read.ptx.sreg.ctaid.y"
blockIdx_z  = special_ptx_reg "llvm.nvvm.read.ptx.sreg.ctaid.z"

laneMask_eq, laneMask_lt, laneMask_le, laneMask_gt, laneMask_ge :: CodeGen (IR Int32)
laneMask_eq = special_ptx_reg "llvm.nvvm.read.ptx.sreg.lanemask.eq"
laneMask_lt = special_ptx_reg "llvm.nvvm.read.ptx.sreg.lanemask.lt"
laneMask_le = special_ptx_reg "llvm.nvvm.read.ptx.sreg.lanemask.le"
laneMask_gt = special_ptx_reg "llvm.nvvm.read.ptx.sreg.lanemask.gt"
laneMask_ge = special_ptx_reg "llvm.nvvm.read.ptx.sreg.lanemask.ge"


-- | NOTE: The special register %warpid as volatile value and is not guaranteed
--         to be constant over the lifetime of a thread or thread block.
--
-- http://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#sm-id-and-warp-id
--
-- http://docs.nvidia.com/cuda/parallel-thread-execution/index.html#special-registers-warpid
--
warpId :: DeviceProperties -> CodeGen (IR Int32)
warpId dev = do
  tid <- threadIdx_x
  -- ws  <- warpSize
  A.quot integralType tid (i32 (CUDA.warpSize dev))

_warpId :: CodeGen (IR Int32)
_warpId = special_ptx_reg "llvm.ptx.read.warpid"

i32 :: Int -> IR Int32
i32 = lift . P.fromIntegral


-- | The size of the thread grid, in each dimension
--
-- > gridDim.x * blockDim.x
--
gridSize_x :: CodeGen (IR Int32)
gridSize_x = gridSizeBy gridDim_x blockDim_x

gridSize_y :: CodeGen (IR Int32)
gridSize_y = gridSizeBy gridDim_y blockDim_y

gridSize_z :: CodeGen (IR Int32)
gridSize_z = gridSizeBy gridDim_z blockDim_z

gridSizeBy :: CodeGen (IR Int32) -> CodeGen (IR Int32) -> CodeGen (IR Int32)
gridSizeBy gridDim blockDim = do
  ncta  <- gridDim
  ntid  <- blockDim
  mul numType ncta ntid


-- | The global thread index, along each dimension
--
-- > blockDim.x * blockIdx.x + threadIdx.x
--
globalThreadIdx_x :: CodeGen (IR Int32)
globalThreadIdx_x = globalThreadIdxBy blockDim_x blockIdx_x threadIdx_x

globalThreadIdx_y :: CodeGen (IR Int32)
globalThreadIdx_y = globalThreadIdxBy blockDim_y blockIdx_y threadIdx_y

globalThreadIdx_z :: CodeGen (IR Int32)
globalThreadIdx_z = globalThreadIdxBy blockDim_z blockIdx_z threadIdx_z

globalThreadIdxBy :: CodeGen (IR Int32) -> CodeGen (IR Int32) -> CodeGen (IR Int32) -> CodeGen (IR Int32)
globalThreadIdxBy blockDim blockIdx threadIdx = do
  ntid  <- blockDim
  ctaid <- blockIdx
  tid   <- threadIdx
  --
  u     <- mul numType ntid ctaid
  v     <- add numType tid u
  return v


-- | Generate kernel function parameters that specify the index range the
-- threads will evaluate.
--
gangParam  :: forall sh. Shape sh => Proxy sh -> (IR sh, [LLVM.Parameter])
gangParam _ =
  let end = "ix.end" :: Name sh
  in  (local end, parameter end)

gangParamFromTo :: forall sh. Shape sh => Proxy sh -> (IR sh, IR sh, [LLVM.Parameter])
gangParamFromTo _ =
  let start = "ix.start" :: Name sh
      end   = "ix.end"   :: Name sh
  in
  (local start, local end, parameter start ++ parameter end )


-- Barriers and synchronisation
-- ----------------------------

-- | Call a builtin CUDA synchronisation intrinsic
--
barrier :: Label -> CodeGen ()
barrier f = void $ call (Body VoidType f) [NoUnwind, NoDuplicate, Convergent]


-- | Wait until all threads in the thread block have reached this point and all
-- global and shared memory accesses made by these threads prior to
-- __syncthreads() are visible to all threads in the block.
--
-- <http://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#synchronization-functions>
--
__syncthreads :: CodeGen ()
__syncthreads = barrier "llvm.nvvm.barrier0"


-- | Ensure that all writes to shared and global memory before the call to
-- __threadfence_block() are observed by all threads in the *block* of the
-- calling thread as occurring before all writes to shared and global memory
-- made by the calling thread after the call.
--
-- <http://docs.nvidia.com/cuda/cuda-c-programming-guide/index.html#memory-fence-functions>
--
__threadfence_block :: CodeGen ()
__threadfence_block = barrier "llvm.nvvm.membar.cta"


-- | As __threadfence_block(), but the synchronisation is for *all* thread blocks.
-- In CUDA this is known simply as __threadfence().
--
__threadfence_grid :: CodeGen ()
__threadfence_grid = barrier "llvm.nvvm.membar.gl"


-- Atomic functions
-- ----------------

-- LLVM provides atomic instructions for integer arguments only. CUDA provides
-- additional support for atomic add on floating point types, which can be
-- accessed through the following intrinsics.
--
-- Double precision is only supported on Compute 6.0 devices and later. LLVM-4.0
-- currently lacks support for this intrinsic, however it may be possible to use
-- inline assembly.
--
-- <https://github.com/AccelerateHS/accelerate/issues/363>
--
atomicAdd_f :: FloatingType a -> Operand (Ptr a) -> Operand a -> CodeGen ()
atomicAdd_f t addr val =
  let
      width :: Int
      width =
        case t of
          TypeHalf{}    -> 16
          TypeFloat{}   -> 32
          TypeDouble{}  -> 64
          TypeCFloat{}  -> 32
          TypeCDouble{} -> 64

      addrspace :: Word32
      (t_addr, t_val, addrspace) =
        case typeOf addr of
          PrimType ta@(PtrPrimType (ScalarPrimType tv) (AddrSpace as))
            -> (ta, tv, as)
          _ -> $internalError "atomicAdd" "unexpected operand type"

      t_ret = PrimType (ScalarPrimType t_val)
      fun   = fromString $ printf "llvm.nvvm.atomic.load.add.f%d.p%df%d" width addrspace width
  in
  void $ call (Lam t_addr addr (Lam (ScalarPrimType t_val) val (Body t_ret fun))) [NoUnwind]


-- Shared memory
-- -------------

sharedMemAddrSpace :: AddrSpace
sharedMemAddrSpace = AddrSpace 3

sharedMemVolatility :: Volatility
sharedMemVolatility = Volatile


-- Declare a new statically allocated array in the __shared__ memory address
-- space, with enough storage to contain the given number of elements.
--
staticSharedMem
    :: forall e. Elt e
    => Word64
    -> CodeGen (IRArray (Vector e))
staticSharedMem n = do
  ad    <- go (eltType (undefined::e))
  return $ IRArray { irArrayShape      = IR (OP_Pair OP_Unit (OP_Int (integral integralType (P.fromIntegral n))))
                   , irArrayData       = IR ad
                   , irArrayAddrSpace  = sharedMemAddrSpace
                   , irArrayVolatility = sharedMemVolatility
                   }
  where
    go :: TupleType s -> CodeGen (Operands s)
    go TypeRunit          = return OP_Unit
    go (TypeRpair t1 t2)  = OP_Pair <$> go t1 <*> go t2
    go tt@(TypeRscalar t) = do
      -- Declare a new global reference for the statically allocated array
      -- located in the __shared__ memory space.
      nm <- freshName
      sm <- return $ ConstantOperand $ GlobalReference (PrimType (PtrPrimType (ArrayPrimType n t) sharedMemAddrSpace)) nm
      declare $ LLVM.globalVariableDefaults
        { LLVM.addrSpace = sharedMemAddrSpace
        , LLVM.type'     = LLVM.ArrayType n (downcast t)
        , LLVM.linkage   = LLVM.External
        , LLVM.name      = downcast nm
        , LLVM.alignment = 4 `P.max` P.fromIntegral (sizeOf tt)
        }

      -- Return a pointer to the first element of the __shared__ memory array.
      -- We do this rather than just returning the global reference directly due
      -- to how __shared__ memory needs to be indexed with the GEP instruction.
      p <- instr' $ GetElementPtr sm [num numType 0, num numType 0 :: Operand Int32]
      q <- instr' $ PtrCast (PtrPrimType (ScalarPrimType t) sharedMemAddrSpace) p

      return $ ir' t (unPtr q)


-- External declaration in shared memory address space. This must be declared in
-- order to access memory allocated dynamically by the CUDA driver. This results
-- in the following global declaration:
--
-- > @__shared__ = external addrspace(3) global [0 x i8]
--
initialiseDynamicSharedMemory :: CodeGen (Operand (Ptr Word8))
initialiseDynamicSharedMemory = do
  declare $ LLVM.globalVariableDefaults
    { LLVM.addrSpace = sharedMemAddrSpace
    , LLVM.type'     = LLVM.ArrayType 0 (LLVM.IntegerType 8)
    , LLVM.linkage   = LLVM.External
    , LLVM.name      = LLVM.Name "__shared__"
    , LLVM.alignment = 4
    }
  return $ ConstantOperand $ GlobalReference (PrimType (PtrPrimType (ArrayPrimType 0 scalarType) sharedMemAddrSpace)) "__shared__"


-- Declared a new dynamically allocated array in the __shared__ memory space
-- with enough space to contain the given number of elements.
--
dynamicSharedMem
    :: forall e int. (Elt e, IsIntegral int)
    => IR int                                 -- number of array elements
    -> IR int                                 -- #bytes of shared memory the have already been allocated
    -> CodeGen (IRArray (Vector e))
dynamicSharedMem n@(op integralType -> m) (op integralType -> offset) = do
  smem <- initialiseDynamicSharedMemory
  let
      go :: TupleType s -> Operand int -> CodeGen (Operand int, Operands s)
      go TypeRunit         i  = return (i, OP_Unit)
      go (TypeRpair t2 t1) i0 = do
        (i1, p1) <- go t1 i0
        (i2, p2) <- go t2 i1
        return $ (i2, OP_Pair p2 p1)
      go (TypeRscalar t)   i  = do
        p <- instr' $ GetElementPtr smem [num numType 0, i] -- TLM: note initial zero index!!
        q <- instr' $ PtrCast (PtrPrimType (ScalarPrimType t) sharedMemAddrSpace) p
        a <- instr' $ Mul numType m (integral integralType (P.fromIntegral (sizeOf (TypeRscalar t))))
        b <- instr' $ Add numType i a
        return (b, ir' t (unPtr q))
  --
  (_, ad) <- go (eltType (undefined::e)) offset
  IR sz   <- A.fromIntegral integralType (numType :: NumType Int) n
  return   $ IRArray { irArrayShape      = IR $ OP_Pair OP_Unit sz
                     , irArrayData       = IR ad
                     , irArrayAddrSpace  = sharedMemAddrSpace
                     , irArrayVolatility = sharedMemVolatility
                     }


-- Global kernel definitions
-- -------------------------

data instance KernelMetadata PTX = KM_PTX LaunchConfig

-- | Combine kernels into a single program
--
(+++) :: IROpenAcc PTX aenv a -> IROpenAcc PTX aenv a -> IROpenAcc PTX aenv a
IROpenAcc k1 +++ IROpenAcc k2 = IROpenAcc (k1 ++ k2)


-- | Create a single kernel program with the default launch configuration.
--
makeOpenAcc
    :: PTX
    -> Label
    -> [LLVM.Parameter]
    -> CodeGen ()
    -> CodeGen (IROpenAcc PTX aenv a)
makeOpenAcc (deviceProperties . ptxContext -> dev) =
  makeOpenAccWith (simpleLaunchConfig dev)

-- | Create a single kernel program with the given launch analysis information.
--
makeOpenAccWith
    :: LaunchConfig
    -> Label
    -> [LLVM.Parameter]
    -> CodeGen ()
    -> CodeGen (IROpenAcc PTX aenv a)
makeOpenAccWith config name param kernel = do
  body  <- makeKernel config name param kernel
  return $ IROpenAcc [body]

-- | Create a complete kernel function by running the code generation process
-- specified in the final parameter.
--
makeKernel :: LaunchConfig -> Label -> [LLVM.Parameter] -> CodeGen () -> CodeGen (Kernel PTX aenv a)
makeKernel config name@(Label l) param kernel = do
  _    <- kernel
  code <- createBlocks
  addMetadata "nvvm.annotations"
    [ Just . MetadataConstantOperand $ LLVM.GlobalReference (LLVM.PointerType (LLVM.FunctionType LLVM.VoidType [ t | LLVM.Parameter t _ _ <- param ] False) (AddrSpace 0)) (LLVM.Name l)
    , Just . MetadataStringOperand   $ "kernel"
    , Just . MetadataConstantOperand $ LLVM.Int 32 1
    ]
  return $ Kernel
    { kernelMetadata = KM_PTX config
    , unKernel       = LLVM.functionDefaults
                     { LLVM.returnType  = LLVM.VoidType
                     , LLVM.name        = downcast name
                     , LLVM.parameters  = (param, False)
                     , LLVM.basicBlocks = code
                     }
    }

