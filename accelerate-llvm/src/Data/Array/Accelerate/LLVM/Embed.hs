{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Embed
-- Copyright   : [2017] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Embed a compiled module together with its associated execution steps as
-- a TemplateHaskell expression. This is a combination of the link and execute
-- steps, so that we do not need to retain the decorated ExecOpenAcc.
--

module Data.Array.Accelerate.LLVM.Embed (

  Embed(..),
  -- embedAfun, embedOpenAfun,
  embedOpenAcc,

) where

import Data.Array.Accelerate.AST                                    ( PrimFun(..), liftArrays, liftConst )
import Data.Array.Accelerate.Array.Representation                   ( SliceIndex(..) )
import Data.Array.Accelerate.Array.Sugar                            hiding ( toIndex, fromIndex, intersect, union, shape, reshape )
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Interpreter                            ( evalPrimConst, evalUndef, evalCoerce )
import Data.Array.Accelerate.Product
import Data.Array.Accelerate.Type
import qualified Data.Array.Accelerate.Array.Sugar                  as Sugar

import Data.Array.Accelerate.LLVM.AST
import Data.Array.Accelerate.LLVM.Array.Data
import Data.Array.Accelerate.LLVM.CodeGen.Environment               as CodeGen ( Gamma, Idx'(..) )
import Data.Array.Accelerate.LLVM.Compile
import Data.Array.Accelerate.LLVM.Embed.Environment
import Data.Array.Accelerate.LLVM.Embed.Extra
import Data.Array.Accelerate.LLVM.Execute
import Data.Array.Accelerate.LLVM.Execute.Async
import Data.Array.Accelerate.LLVM.Execute.Environment               as Exec
import Data.Array.Accelerate.LLVM.Extra
import Data.Array.Accelerate.LLVM.Link

import Data.Bits
import Data.Char
import Control.Monad                                                ( foldM )
import Data.Either
import Data.Typeable
import Language.Haskell.TH                                          ( Q )
import qualified Language.Haskell.TH                                as TH
import qualified Language.Haskell.TH.Syntax                         as TH

#if MIN_VERSION_containers(0,5,9)
import qualified Data.IntMap.Internal                               as IM
#elif MIN_VERSION_containers(0,5,8)
import qualified Data.IntMap.Base                                   as IM
#else
import qualified Data.IntMap                                        as IM
#endif
import Prelude                                                      hiding ( exp, map, sum, scanl, scanl1, scanr, scanr1, init, unzip, uncurry )
import qualified Prelude                                            as P


class Embed arch where

  -- | Turn the compiled object into a TemplateHaskell expression, suitable for
  -- use in a splice. The splice should evaluate into the backend-specific
  -- executable representation.
  --
  embedForTarget
      :: arch
      -> ObjectR arch
      -> TExpQ (ExecutableR arch)


-- Array computations
-- ------------------

-- | Embed a compiled array function into a TemplateHaskell expression ready for
-- direct execution.
--
{-# INLINE embedOpenAcc #-}   -- GHC bug? Specialisations should be possible with INLINEABLE, but we require INLINE
embedOpenAcc
    :: forall arch aenv arrs. (Embed arch, Execute arch, Async arch, Typeable arch, Typeable aenv, Typeable arrs, Typeable (FutureR arch))
    => arch                                       -- ^ target architecture this code was compiled for
    -> CompiledOpenAcc arch aenv arrs             -- ^ compiled syntax tree
    -> AvalQ arch aenv                            -- ^ environment of bindings
    -> TExpQ (Par arch (FutureR arch arrs))
embedOpenAcc arch acc aenv = liftA acc
  where
    liftA :: CompiledOpenAcc arch aenv arrs -> TExpQ (Par arch (FutureR arch arrs))
    liftA (PlainAcc pacc)           = withSigE $ embedPreOpenAccCommand  arch                                 pacc aenv
    liftA (BuildAcc gamma obj pacc) = withSigE $ embedPreOpenAccSkeleton arch gamma (embedForTarget arch obj) pacc aenv


{-# INLINEABLE embedPreOpenAccCommand #-}
embedPreOpenAccCommand
    :: forall arch aenv arrs. (Embed arch, Execute arch, Async arch, Typeable arch, Typeable aenv, Typeable (FutureR arch))
    => arch
    -> PreOpenAccCommand CompiledOpenAcc arch aenv arrs
    -> AvalQ arch aenv
    -> TExpQ (Par arch (FutureR arch arrs))
embedPreOpenAccCommand arch pacc aenv =
  case pacc of
    Alet bnd body       -> alet bnd body
    Avar ix             -> [|| return $$(aprjQ ix aenv) ||]
    Use arrs            -> [|| spawn $ useRemoteAsync (toArr $$(liftArrays (arrays @arrs) arrs)) ||]
    Unit x              -> unit x
    Atuple tup          -> atuple tup
    Aprj ix tup         -> liftF1 (aprj ix) (travA tup)
    Alloc sh            -> alloc sh
    -- Apply f a           -> error "apply"
    -- Acond p t e         -> error "acond"
    -- Awhile p f a        -> error "awhile"
    Reshape sh ix       -> reshape sh (aprjQ ix aenv)
    Unzip tix ix        -> liftF1 (unzip tix) [|| return $$(aprjQ ix aenv) ||]
    -- Aforeign str asm a  -> error "aforeign"

  where
    travE :: PreExp (CompiledOpenAcc arch) aenv t -> Q (EventuallyR arch t)
    travE exp = embedPreExp arch exp aenv

    travA :: Arrays a => CompiledOpenAcc arch aenv a -> TExpQ (Par arch (FutureR arch a))
    travA acc = embedOpenAcc arch acc aenv

    alet :: (Arrays a, Arrays b)
         => CompiledOpenAcc arch aenv a
         -> CompiledOpenAcc arch (aenv, a) b
         -> TExpQ (Par arch (FutureR arch b))
    alet bnd body = do
     x  <- newTName "x"
     --
     doE [ bindS (varP x) [|| spawn $ $$( travA bnd ) ||]
         , noBindS [|| spawn $ $$( embedOpenAcc arch body (aenv `ApushQ` varE x) ) ||]
         ]

    unit :: Elt t => PreExp (CompiledOpenAcc arch) aenv t -> TExpQ (Par arch (FutureR arch (Scalar t)))
    unit x = do
      x' <- travE x
      case x' of
        Now   v -> [|| newRemoteAsync Z (const $$v) ||]
        Later v -> [|| do u <- $$v
                          spawn $ newRemoteAsync Z . const =<< get u
                    ||]

    atuple :: Atuple (CompiledOpenAcc arch aenv) (TupleRepr arrs) -> TExpQ (Par arch (FutureR arch arrs))
    atuple atup = do
      let
          go :: Atuple (CompiledOpenAcc arch aenv) arrs' -> [TH.ExpQ]
          go NilAtup         = []
          go (SnocAtup as a) = TH.unTypeQ (travA a) : go as
          --
          atup' = reverse (go atup)  -- XXX: tuples are snoc-lists
      --
      us  <- sequence [ TH.newName ('u' : show i) | i <- [1 .. P.length atup'] ]
      vs  <- sequence [ TH.newName ('v' : show i) | i <- [1 .. P.length atup'] ]
      r   <- newTName "r"
      doE $ P.zipWith (\u a -> bindS (TH.varP u) [|| $$spawn_ $$(unsafeTExpCoerce a) ||]) us atup' ++
          [ bindS (varP r) new_
          , noBindS [|| $$fork_ $ $$( doE $ P.zipWith (\v u -> bindS (TH.varP v) [|| $$get_ $$(varE (TName u)) ||]) vs us ++
                                          [ noBindS [|| $$put_ $$(varE r) $$(unsafeTExpCoerce (TH.tupE (P.map TH.varE vs))) ||] ]
                                    )
                     ||]
          , noBindS [|| $$return_ $$(varE r) ||]
          ]

    aprj :: forall t a. IsAtuple t => TupleIdx (TupleRepr t) a -> TExpQ t -> TExpQ a
    aprj tix arrs = do
      a <- TH.newName "a"
      let
          width :: ProdR Arrays s -> Int
          width ProdRunit     = 0
          width (ProdRsnoc p) = 1 + width p

          pat :: TupleIdx u v -> [TH.PatQ] -> [TH.PatQ]
          pat ZeroTupIdx      (_:xs) = TH.varP a : xs
          pat (SuccTupIdx ix) (x:xs) = x : pat ix xs
          pat _               []     = $internalError "aprj" "inconsistent valuation"

          ignores = replicate (width (prod @Arrays @t)) TH.wildP
      --
      TH.unsafeTExpCoerce $
        TH.caseE (TH.unTypeQ arrs) [ TH.match (TH.tupP (reverse (pat tix ignores))) (TH.normalB (TH.varE a)) [] ]

    alloc :: (Shape sh, Elt e) => PreExp (CompiledOpenAcc arch) aenv sh -> TExpQ (Par arch (FutureR arch (Array sh e)))
    alloc sh = do
      sh' <- travE sh
      case sh' of
        Now   v -> [|| newFull =<< allocateRemote $$v ||]
        Later v -> [|| do u <- $$v
                          r <- new
                          fork $ do
                            arr <- allocateRemote =<< get u
                            put r arr
                          return r
                    ||]

    reshape :: (Shape sh, Shape sh', Elt e)
            => PreExp (CompiledOpenAcc arch) aenv sh
            -> TExpQ           (FutureR arch (Array sh' e))
            -> TExpQ (Par arch (FutureR arch (Array sh  e)))
    reshape sh arr = do
      sh' <- travE sh
      case sh' of
        Now   v -> [|| do r <- new
                          fork $ do
                            arr' <- get $$arr
                            put r (Sugar.reshape $$v arr')
                          return r ||]
        Later v -> [|| do u <- $$v
                          r <- new
                          fork $ do
                            arr' <- get $$arr
                            u'   <- get u
                            put r (Sugar.reshape u' arr')
                          return r ||]

    unzip :: forall sh t e. (Elt t, Elt e) => TupleIdx (TupleRepr t) e -> TExpQ (Array sh t) -> TExpQ (Array sh e)
    unzip tix arr = do
      sh      <- TH.newName "sh"
      (ad, v) <- pat tix (eltType @t)
      unsafeTExpCoerce $
        TH.caseE (TH.unTypeQ arr)
          [ TH.match (TH.conP 'Array [TH.varP sh, ad]) (TH.normalB [| Array $(TH.varE sh) $(TH.varE v)|]) [] ]
      where
        pat :: TupleIdx v e -> TupleType t' -> Q (TH.PatQ, TH.Name)
        pat ZeroTupIdx      (TypeRpair _ _) = do v      <- TH.newName "x"
                                                 return ( TH.conP 'AD_Pair [TH.wildP, TH.varP v], v )
        pat (SuccTupIdx ix) (TypeRpair t _) = do (p, v) <- pat ix t
                                                 return ( TH.conP 'AD_Pair [p, TH.wildP], v )
        pat _               _               = $internalError "unzip" "inconsistent valuation"

    liftF1 :: (TExpQ a -> TExpQ b)
           -> TExpQ (Par arch (FutureR arch a))
           -> TExpQ (Par arch (FutureR arch b))
    liftF1 f x = do
      r <- newTName "r"
      u <- newTName "x"
      v <- newTName "y"
      doE [ bindS (varP r) new_
          , bindS (varP u) x
          , noBindS [|| $$fork_ $ $$( doE [ bindS (varP v) [|| $$get_ $$(varE u) ||]
                                          , noBindS [|| $$put_ $$(varE r) $$(f (varE v)) ||]
                                          ])
                     ||]
          , noBindS [|| $$return_ $$(varE r) ||]
          ]

    -- XXX: Hacks to get Typed TemplateHaskell to type check
    --
    new_ :: TExpQ (Par arch (FutureR arch a))
    new_ = varE (TName 'new)

    fork_ :: TExpQ (Par arch () -> Par arch ())
    fork_ = varE (TName 'fork)

    put_ :: TExpQ (FutureR arch a -> a -> Par arch ())
    put_ = varE (TName 'put)

    get_ :: TExpQ (FutureR arch a -> Par arch a)
    get_ = varE (TName 'get)

    spawn_ :: TExpQ (Par arch (FutureR arch a) -> Par arch (FutureR arch a))
    spawn_ = varE (TName 'spawn)

    return_ :: TExpQ (a -> Par arch a)
    return_ = varE (TName 'return)


{-# INLINEABLE embedPreOpenAccSkeleton #-}
embedPreOpenAccSkeleton
    :: forall arch aenv arrs. (Embed arch, Execute arch, Async arch, Typeable arch, Typeable aenv, Typeable (FutureR arch))
    => arch
    -> CodeGen.Gamma aenv
    -> TExpQ (ExecutableR arch)
    -> PreOpenAccSkeleton CompiledOpenAcc arch aenv arrs
    -> AvalQ arch aenv
    -> TExpQ (Par arch (FutureR arch arrs))
embedPreOpenAccSkeleton arch gamma kernel pacc aenv =
  case pacc of
    -- Producers
    Map sh              -> exec1 'map         (travE sh)
    Generate sh         -> exec1 'generate    (travE sh)
    Transform sh        -> exec1 'transform   (travE sh)
    Backpermute sh      -> exec1 'backpermute (travE sh)

    -- Consumers
    Fold sh             -> exec1 'fold      (travE sh)
    Fold1 sh            -> exec1 'fold1     (travE sh)
    FoldSeg sa ss       -> exec2 'foldSeg   (travE sa) (travE ss)
    Fold1Seg sa ss      -> exec2 'fold1Seg  (travE sa) (travE ss)
    Scanl sh            -> exec1 'scanl     (travE sh)
    Scanr sh            -> exec1 'scanr     (travE sh)
    Scanl1 sh           -> exec1 'scanl1    (travE sh)
    Scanr1 sh           -> exec1 'scanr1    (travE sh)
    Scanl' sh           -> exec1 'scanl'    (travE sh)
    Scanr' sh           -> exec1 'scanr'    (travE sh)
    -- Permute sh d        -> exec2 (permute (inplace d)) (travE sh) (travA d)
    -- Stencil1 h sh       -> exec1 (stencil1 h) (travE sh)
    -- Stencil2 h sh1 sh2  -> exec2 (stencil2 h) (travE sh2) (travE sh1)

  where
    travE :: PreExp (CompiledOpenAcc arch) aenv t -> Q (EventuallyR arch t)
    travE exp = embedPreExp arch exp aenv

    exec1 :: TH.Name    -- ExecutableR arch -> Gamma aenv -> a -> Par arch (FutureR arch b)
          -> Q (EventuallyR arch a)
          -> TExpQ (Par arch (FutureR arch b))
    exec1 (return . TH.TExp . TH.VarE -> f) x = do
      x'      <- x
      u       <- newTName "u"
      v       <- newTName "v"
      (ss, g) <- liftGamma gamma
      case x' of
        Now r   -> [|| spawn $ $$( doE $ ss ++
                                       [ noBindS [|| $$f $$kernel $$g $$r ||] ]) ||]
        Later r -> doE [ bindS (varP u) r
                       , noBindS [|| $$spawn_ $ $$( doE $ ss ++
                                                        [ bindS (varP v) [|| $$get_ $$(varE u) ||]
                                                        , noBindS [|| $$f $$kernel $$g $$(varE v) ||]
                                                        ])
                                  ||]
                       ]

    exec2 :: TH.Name    -- ExecutableR arch -> Gamma aenv -> a -> b -> Par arch (FutureR arch c)
          -> Q (EventuallyR arch a)
          -> Q (EventuallyR arch b)
          -> TExpQ (Par arch (FutureR arch c))
    exec2 (return . TH.TExp . TH.VarE -> f) x y = do
      x'      <- x
      y'      <- y
      u1      <- newTName "u"
      v1      <- newTName "v"
      u2      <- newTName "u"
      v2      <- newTName "v"
      (ss, g) <- liftGamma gamma
      let
          go (Now a) (Now b)      = [|| spawn $ $$( doE $ ss ++
                                                        [ noBindS [|| $$f $$kernel $$g $$a $$b ||] ]) ||]

          go (Now a) (Later b)    = doE [ bindS (varP u2) b
                                        , noBindS [|| $$spawn_ $ $$( doE $ ss ++
                                                                         [ bindS (varP v2) [|| $$get_ $$(varE u2) ||]
                                                                         , noBindS [|| $$f $$kernel $$g $$a $$(varE v2) ||]
                                                                         ]) ||]
                                        ]

          go (Later a) (Now b)    = doE [ bindS (varP u1) a
                                        , noBindS [|| $$spawn_ $ $$( doE $ ss ++
                                                                         [ bindS (varP v1) [|| $$get_ $$(varE u1) ||]
                                                                         , noBindS [|| $$f $$kernel $$g $$(varE v1) $$b ||]
                                                                         ]) ||]
                                        ]
          go (Later a) (Later b)  = doE [ bindS (varP u1) a
                                        , bindS (varP u2) b
                                        , noBindS [|| $$spawn_ $ $$( doE $ ss ++
                                                                         [ bindS (varP v1) [|| $$get_ $$(varE u1) ||]
                                                                         , bindS (varP v2) [|| $$get_ $$(varE u2) ||]
                                                                         , noBindS [|| $$f $$kernel $$g $$(varE v1) $$(varE v2) ||]
                                                                         ]) ||]
                                        ]
      --
      go x' y'

    liftGamma :: CodeGen.Gamma aenv -> Q ([TH.StmtQ], TExpQ (Exec.Gamma aenv))
    liftGamma im = do
      let
          go :: ([TH.StmtQ], TH.ExpQ, TH.ExpQ) -> Idx' aenv -> Q ([TH.StmtQ], TH.ExpQ, TH.ExpQ)
          go (ss, aeR, as) (Idx' idx) = do
            a <- newTName "a"
            let
                s     = bindS (varP a) [|| $$get_ $$(aprjQ idx aenv) ||]
                aeR'  = [| ArraysRpair $aeR ArraysRarray |]
                as'   = [| ($as, $(TH.unTypeQ (varE a))) |]
            --
            return ( s:ss, aeR', as')
      --
      (ss, aeR, as) <- foldM go ([], [| ArraysRunit |], [| () |]) [ ix | (_, ix) <- IM.elems im ]
      return (ss, TH.unsafeTExpCoerce [| Gamma $aeR $as |])

    -- XXX: Hacks to get Typed TemplateHaskell to type check
    --
    get_ :: TExpQ (FutureR arch a -> Par arch a)
    get_ = varE (TName 'get)

    spawn_ :: TExpQ (Par arch (FutureR arch a) -> Par arch (FutureR arch a))
    spawn_ = varE (TName 'spawn)


-- Scalar expressions
-- ------------------

-- When evaluating scalar expressions we keep track of whether this value is
-- available immediately (e.g. primitive function application), or might have
-- been evaluated asynchronously (e.g. reading a value from an array). This
-- distinction affects what kind of code is generated, but otherwise does not
-- exist at runtime.
--
data EventuallyR arch a
  = Now   (TExpQ a)
  | Later (TExpQ (Par arch (FutureR arch a)))

-- Embed a scalar expression.
--
-- In contrast to the execution phase, where we always return values as futures,
-- since this operation runs at compile time it is worthwhile distinguishing the
-- cases where we know this is a real value that can be used immediately.
--
-- If we do the same at execution time, we just add another layer of
-- indirection, but here the 'Either' does not appear at runtime, it just guides
-- the code which is to be generated.
--
-- XXX: Strictly speaking, we ought to do the same thing as the LLVM code
-- generator and keep track of collections of scalar values (as in 'IR'). Here,
-- we just have a single 'TExp' for each value; this means we need to a bit of
-- extra work when packing into/out of tuples for example (I'm not sure if GHC
-- is smart enough to simplify such expressions). This would also improve our
-- ability to keep track of types (e.g. 'indexSlice', 'indexFull')
--
{-# INLINEABLE embedPreExp #-}
embedPreExp
    :: forall arch aenv exp. (Embed arch, Execute arch, Async arch, Typeable arch, Typeable aenv, Typeable (FutureR arch))
    => arch
    -> PreExp (CompiledOpenAcc arch) aenv exp
    -> AvalQ arch aenv
    -> Q (EventuallyR arch exp)
embedPreExp arch exp = embedPreOpenExp arch exp EmptyQ

{-# INLINEABLE embedPreOpenExp #-}
embedPreOpenExp
    :: forall arch env aenv exp. (Embed arch, Execute arch, Async arch, Typeable arch, Typeable env, Typeable aenv, Typeable (FutureR arch))
    => arch
    -> CompiledOpenExp arch env aenv exp
    -> ValQ arch env
    -> AvalQ arch aenv
    -> Q (EventuallyR arch exp)
embedPreOpenExp arch exp env aenv =
  case exp of
    Let bnd body            -> elet bnd body
    Var ix                  -> now (prjQ ix env)
    Undef                   -> now [|| evalUndef ||]
    Const c                 -> now $ withSigE [|| toElt $$(liftConst (eltType @exp) c) ||]
    PrimConst c             -> now $ withSigE [|| toElt $$(liftConst (eltType @exp) (fromElt (evalPrimConst c))) ||]
    PrimApp f x             -> lift1 (now . embedPrimFun f) (travE x)
    Tuple t                 -> etuple t
    Prj ix e                -> lift1 (now . eprj ix) (travE e)
    Cond p t e              -> cond (travE p) (travE t) (travE e)
    -- While p f x
    IndexAny                -> now [|| Any ||]
    IndexNil                -> now [|| Z ||]
    IndexCons sh sz         -> lift2 (now $$ indexCons) (travE sh) (travE sz)
    IndexHead sh            -> lift1 (now .  indexHead) (travE sh)
    IndexTail sh            -> lift1 (now .  indexTail) (travE sh)
    IndexSlice ix slix sh   -> lift2 (now $$ indexSlice ix) (travE slix) (travE sh)
    IndexFull ix slix sl    -> lift2 (now $$ indexFull ix) (travE slix) (travE sl)
    ToIndex sh ix           -> lift2 (now $$ toIndex) (travE sh) (travE ix)
    FromIndex sh ix         -> lift2 (now $$ fromIndex) (travE sh) (travE ix)
    Intersect sh1 sh2       -> lift2 (now $$ intersect) (travE sh1) (travE sh2)
    Union sh1 sh2           -> lift2 (now $$ union) (travE sh1) (travE sh2)
    ShapeSize sh            -> lift1 (now . shapeSize) (travE sh)
    Shape acc               -> shape (travA acc)
    Index acc ix            -> index (travA acc) (travE ix)
    LinearIndex acc ix      -> linearIndex (travA acc) (travE ix)
    Coerce v                -> lift1 (\x -> now [|| evalCoerce $$x ||]) (travE v)
    Foreign _ f x           -> foreignE f (travE x)

  where
    now :: TExpQ t -> Q (EventuallyR arch t)
    now = return . Now

    later :: TExpQ (Par arch (FutureR arch t)) -> Q (EventuallyR arch t)
    later = return . Later

    travA :: Arrays a => CompiledOpenAcc arch aenv a -> TExpQ (Par arch (FutureR arch a))
    travA a = embedOpenAcc arch a aenv

    travE :: Elt t => CompiledOpenExp arch env aenv t -> Q (EventuallyR arch t)
    travE e = embedPreOpenExp arch e env aenv

    etuple :: Tuple (CompiledOpenExp arch env aenv) (TupleRepr t) -> Q (EventuallyR arch t)
    etuple tup = do
      let
          -- collect the individual expressions, and remember which ones need to
          -- be evaluated as futures.
          --
          go :: Tuple (CompiledOpenExp arch env aenv) t' -> Q [(Bool, TH.ExpQ)]
          go NilTup         = return []
          go (SnocTup es e) = do
            es' <- go es
            e'  <- travE e
            case e' of
              Now x   -> return $ (False, TH.unTypeQ x) : es'
              Later x -> return $ (True,  TH.unTypeQ x) : es'

      tup' <- reverse <$> go tup    -- XXX: tuples are snoc-lists

      if any fst tup'
        -- Some expressions are evaluated as futures
        then do
          let
              go1 []         = return []
              go1 ((p,e):es) = do
                us' <- go1 es
                u'  <- case p of
                         False -> return (Left e)
                         True  -> do
                           u <- TH.newName "u"
                           return $ Right (u, TH.bindS (TH.varP u) e)
                --
                return $ u':us'

              go2 []     = return []
              go2 (e:es) = do
                vs' <- go2 es
                v'  <- case e of
                         Left x      -> return (Left x)
                         Right (u,_) -> do
                           v <- TH.newName "v"
                           return $ Right (v, TH.bindS (TH.varP v) [| get $(TH.varE u) |])
                --
                return (v':vs')

          --
          x1  <- go1 tup'
          x2  <- go2 x1
          r   <- newTName "r"
          later $ doE
                $ P.map snd (rights x1) ++
                [ bindS (varP r) new_
                , TH.noBindS [| fork $ $( TH.doE $ P.map snd (rights x2) ++
                                                 [ noBindS [|| $$put_ $$(varE r) $$(unsafeTExpCoerce (TH.tupE (P.map (either id (TH.varE . fst)) x2))) ||]
                                                 ]
                                        ) |]
                , noBindS [|| $$return_ $$(varE r) ||]
                ]

        -- All expressions are available immediately
        else
          now . unsafeTExpCoerce $ TH.tupE (P.map snd tup')


    -- Helpers
    -- -------
    elet :: (Elt a, Elt b)
         => CompiledOpenExp arch env      aenv a
         -> CompiledOpenExp arch (env, a) aenv b
         -> Q (EventuallyR arch b)
    elet bnd body =
      flip lift1 (travE bnd) $ \x ->
      embedPreOpenExp arch body (env `PushQ` x) aenv

    eprj :: forall t e. IsTuple t => TupleIdx (TupleRepr t) e -> TExpQ t -> TExpQ e
    eprj tix t = do
      x <- TH.newName "x"
      let
          width :: TupleR s -> Int
          width ProdRunit     = 0
          width (ProdRsnoc p) = 1 + width p

          pat :: TupleIdx u v -> [TH.PatQ] -> [TH.PatQ]
          pat ZeroTupIdx      (_:is) = TH.varP x : is
          pat (SuccTupIdx ix) (i:is) = i : pat ix is
          pat _               []     = $internalError "prj" "inconsistent valuation"

          ignores = replicate (width (tuple @t)) TH.wildP
      --
      TH.unsafeTExpCoerce $
        TH.caseE (TH.unTypeQ t) [ TH.match (TH.tupP (reverse (pat tix ignores))) (TH.normalB (TH.varE x)) [] ]

    cond :: Q (EventuallyR arch Bool)
         -> Q (EventuallyR arch a)
         -> Q (EventuallyR arch a)
         -> Q (EventuallyR arch a)
    cond =
      lift3 (\p t e -> now [|| if $$p then $$t else $$e ||])

    indexCons :: TExpQ sh -> TExpQ sz -> TExpQ (sh :. sz)
    indexCons sh sz = [|| $$sh :. $$sz ||]

    indexHead :: TExpQ (sh :. sz) -> TExpQ sz
    indexHead sh = [|| case $$sh of
                         _ :. iz -> iz ||]

    indexTail :: TExpQ (sh :. sz) -> TExpQ sh
    indexTail sh = [|| case $$sh of
                         ih :. _ -> ih ||]

    indexSlice :: forall slix sl co sh. (Elt slix, Shape sh, Shape sl)
               => SliceIndex (EltRepr slix) (EltRepr sl) co (EltRepr sh)
               -> TExpQ slix
               -> TExpQ sh
               -> TExpQ sl
    indexSlice ix _slix sh = do
      let
          pat :: [TH.Name] -> TH.PatQ
          pat = foldl (\a b -> TH.conP '(:.) [a, TH.varP b]) (TH.conP 'Z [])

          restrict :: SliceIndex slix' sl' co' sh' -> [TH.Name] -> TH.ExpQ
          restrict SliceNil              []      = [| Z |]
          restrict (SliceAll   sliceIdx) (sz:sl) = [| $(restrict sliceIdx sl) :. $(TH.varE sz) |]
          restrict (SliceFixed sliceIdx) (_ :sl) = restrict sliceIdx sl
          restrict _                     _       = $internalError "indexSlice" "unexpected valuation"
      --
      sh' <- sequence [ TH.newName ("_sh" ++ show i) | i <- [1 .. rank @sh] ]
      TH.unsafeTExpCoerce
        $ TH.caseE (TH.unTypeQ sh) [ TH.match (pat sh') (TH.normalB (restrict ix (reverse sh'))) [] ]

    indexFull :: forall slix sh co sl. (Elt slix, Shape sh, Shape sl)
              => SliceIndex (EltRepr slix) (EltRepr sl) co (EltRepr sh)
              -> TExpQ slix
              -> TExpQ sl
              -> TExpQ sh
    indexFull ix slix sl = do
      let
          pat :: [TH.Name] -> TH.PatQ
          pat = foldl (\a b -> TH.conP '(:.) [a, TH.varP b]) (TH.conP 'Z [])

          width :: TupleType t -> Int
          width TypeRunit       = 0
          width (TypeRpair t _) = 1 + width t
          width TypeRscalar{}   = $internalError "indexFull" "unexpected valuation"

          extend :: SliceIndex slix' sl' co' sh' -> [TH.Name] -> [TH.Name] -> TH.ExpQ
          extend SliceNil              []       []      = [| Z |]
          extend (SliceAll   sliceIdx) (_ :slx) (sz:sh) = [| $(extend sliceIdx slx sh) :. $(TH.varE sz) |]
          extend (SliceFixed sliceIdx) (sz:slx) sh      = [| $(extend sliceIdx slx sh) :. $(TH.varE sz) |]
          extend _                     _        _       = $internalError "indexFull" "unexpected valuation"
      --
      slix' <- sequence [ TH.newName ("_slix" ++ show i) | i <- [1 .. width (eltType @slix) ] ]
      sl'   <- sequence [ TH.newName ("sl"    ++ show i) | i <- [1 .. rank @sl] ]
      TH.unsafeTExpCoerce
        $ TH.caseE (TH.unTypeQ slix) [ TH.match (pat slix') (TH.normalB (
          TH.caseE (TH.unTypeQ sl)   [ TH.match (pat sl')   (TH.normalB (extend ix (reverse slix') (reverse sl'))) [] ])) [] ]

    toIndex :: Shape sh => TExpQ sh -> TExpQ sh -> TExpQ Int
    toIndex sh ix = [|| Sugar.toIndex $$sh $$ix ||]

    fromIndex :: Shape sh => TExpQ sh -> TExpQ Int -> TExpQ sh
    fromIndex sh ix = [|| Sugar.fromIndex $$sh $$ix ||]

    intersect :: forall sh. Shape sh => TExpQ sh -> TExpQ sh -> TExpQ sh
    -- intersect sh1 sh2 = [|| Sugar.intersect $$sh1 $$sh2 ||]
    intersect sh1 sh2 = do
      (pat1, sh1')  <- shape_pattern @sh
      (pat2, sh2')  <- shape_pattern @sh
      TH.unsafeTExpCoerce
        $ TH.caseE (TH.unTypeQ sh1) [ TH.match pat1 (TH.normalB (
          TH.caseE (TH.unTypeQ sh2) [ TH.match pat2 (TH.normalB ( P.foldl (\a b -> [| $a :. $b |]) (TH.conE 'Z)
                                                                $ P.zipWith (\a b -> [| min $(TH.varE a) $(TH.varE b) |]) sh1' sh2')) [] ])) [] ]

    union :: forall sh. Shape sh => TExpQ sh -> TExpQ sh -> TExpQ sh
    -- union sh1 sh2 = [|| Sugar.union $$sh1 $$sh2 ||]
    union sh1 sh2 = do
      (pat1, sh1')  <- shape_pattern @sh
      (pat2, sh2')  <- shape_pattern @sh
      TH.unsafeTExpCoerce
        $ TH.caseE (TH.unTypeQ sh1) [ TH.match pat1 (TH.normalB (
          TH.caseE (TH.unTypeQ sh2) [ TH.match pat2 (TH.normalB ( P.foldl (\a b -> [| $a :. $b |]) (TH.conE 'Z)
                                                                $ P.zipWith (\a b -> [| max $(TH.varE a) $(TH.varE b) |]) sh1' sh2')) [] ])) [] ]

    shapeSize :: forall sh. Shape sh => TExpQ sh -> TExpQ Int
    -- shapeSize sh = [|| Sugar.size $$sh ||]
    shapeSize sh = do
      (pat, sh')  <- shape_pattern @sh
      case sh' of
        [] -> [|| 1 ||]
        _  -> TH.unsafeTExpCoerce
            $ TH.caseE (TH.unTypeQ sh) [ TH.match pat (TH.normalB (P.foldl1 (\a b -> [| $a * $b|]) (P.map TH.varE sh'))) []]

    shape_pattern :: forall sh. Shape sh => Q (TH.PatQ, [TH.Name])
    shape_pattern = go (eltType @sh)
      where
        go :: TupleType t -> Q (TH.PatQ, [TH.Name])
        go TypeRunit          = return (TH.conP 'Z [], [])
        go (TypeRpair sh sz)  = do
          (psh, sh')  <- go sh
          (psz, sz')  <- go sz
          return (TH.conP '(:.) [psh, psz], sh'++sz')
        go TypeRscalar{}
          = do i' <- TH.newName "sh"
               return (TH.varP i', [i'])

    shape :: Shape sh => TExpQ (Par arch (FutureR arch (Array sh e))) -> Q (EventuallyR arch sh)
    shape (later -> arr) =
      flip lift1 arr $ \a ->
      return $ Now (shape' a)

    shape' :: forall sh e. Shape sh => TExpQ (Array sh e) -> TExpQ sh
    shape' arr = do
      let
          go :: TupleType t -> Q (TH.PatQ, [TH.Name])
          go TypeRunit          = return (TH.tupP [], [])
          go (TypeRpair sh sz)  = do
            (psh, sh')  <- go sh
            (psz, sz')  <- go sz
            return (TH.tupP [psh, psz], sh'++sz')
          go TypeRscalar{}
            = do i' <- TH.newName "sh"
                 return (TH.varP i', [i'])
      --
      (pat, sh) <- go (eltType @sh)
      TH.unsafeTExpCoerce $
        TH.caseE (TH.unTypeQ arr)
          [ TH.match (TH.conP 'Array [pat, TH.wildP])
                     (TH.normalB $ foldl (\a b -> [| $a :. $(TH.varE b) |]) (TH.conE 'Z) sh)
                     []
          ]

    index :: (Shape sh, Elt e) => TExpQ (Par arch (FutureR arch (Array sh e))) -> Q (EventuallyR arch sh) -> Q (EventuallyR arch e)
    index (later -> arr) ix =
      lift2 (\arr' ix' -> later [|| indexRemoteAsync $$arr' (Sugar.toIndex (Sugar.shape $$arr') $$ix') ||]) arr ix

    linearIndex :: Elt e => TExpQ (Par arch (FutureR arch (Array sh e))) -> Q (EventuallyR arch Int) -> Q (EventuallyR arch e)
    linearIndex (later -> arr) ix =
      lift2 (\arr' ix' -> later [|| indexRemoteAsync $$arr' $$ix' ||]) arr ix

    foreignE :: CompiledFun arch () (a -> b) -> Q (EventuallyR arch a) -> Q (EventuallyR arch b)
    foreignE (Lam (Body f)) = lift1 (\x -> embedPreOpenExp arch f (EmptyQ `PushQ` x) AemptyQ)
    foreignE _              = error "will you still love me, when I'm no longer young and beautiful?"

    lift1 :: (TExpQ a -> Q (EventuallyR arch b))
          -> Q (EventuallyR arch a)
          -> Q (EventuallyR arch b)
    lift1 f a = do
      a' <- a
      case a' of
        Now x -> do
          u  <- newTName "x"
          b' <- f (varE u)
          case b' of
            Now y ->
              now $ letE [ valD (varP u) (normalB x) [] ] y
            --
            Later y ->
              later $
                doE [ letS [ valD (varP u) (normalB x) [] ]
                    , noBindS y
                    ]
        --
        Later x -> do
          u  <- newTName "x"
          u' <- newTName "x'"
          r  <- newTName "r"
          b' <- f (varE u')
          case b' of
            Now y ->
              later $
                doE [ bindS (varP r) new_
                    , bindS (varP u) x
                    , noBindS [|| $$fork_ $$( doE [ bindS (varP u') [|| $$get_ $$(varE u) ||]
                                                  , noBindS [|| $$put_ $$(varE r) $$y ||]
                                                  ])
                               ||]
                    , noBindS [|| $$return_ $$(varE r) ||]
                    ]
            --
            Later y ->
              later $
                doE [ bindS (varP u) x
                    , noBindS [|| $$spawn_ $$( doE [ bindS (varP u') [|| $$get_ $$(varE u) ||]
                                                   , noBindS y
                                                   ])
                               ||]
                    ]

    lift2 :: (TExpQ a -> TExpQ b -> Q (EventuallyR arch c))
          -> Q (EventuallyR arch a)
          -> Q (EventuallyR arch b)
          -> Q (EventuallyR arch c)
    lift2 f a b =
      flip lift1 a $ \x ->
      flip lift1 b $ \y ->
        f x y

    lift3 :: (TExpQ a -> TExpQ b -> TExpQ c -> Q (EventuallyR arch d))
          -> Q (EventuallyR arch a)
          -> Q (EventuallyR arch b)
          -> Q (EventuallyR arch c)
          -> Q (EventuallyR arch d)
    lift3 f a b c =
      flip lift1 a $ \x ->
      flip lift1 b $ \y ->
      flip lift1 c $ \z ->
        f x y z

    -- XXX: Hacks to get Typed TemplateHaskell to type check
    --
    new_ :: TExpQ (Par arch (FutureR arch a))
    new_ = varE (TName 'new)

    fork_ :: TExpQ (Par arch () -> Par arch ())
    fork_ = varE (TName 'fork)

    put_ :: TExpQ (FutureR arch a -> a -> Par arch ())
    put_ = varE (TName 'put)

    get_ :: TExpQ (FutureR arch a -> Par arch a)
    get_ = varE (TName 'get)

    spawn_ :: TExpQ (Par arch (FutureR arch a) -> Par arch (FutureR arch a))
    spawn_ = varE (TName 'spawn)

    return_ :: TExpQ (a -> Par arch a)
    return_ = varE (TName 'return)


{-# INLINEABLE embedPrimFun #-}
embedPrimFun :: PrimFun (a -> b) -> TExpQ a -> TExpQ b
embedPrimFun (PrimAdd                ty) = embedAdd ty
embedPrimFun (PrimSub                ty) = embedSub ty
embedPrimFun (PrimMul                ty) = embedMul ty
embedPrimFun (PrimNeg                ty) = embedNeg ty
embedPrimFun (PrimAbs                ty) = embedAbs ty
embedPrimFun (PrimSig                ty) = embedSig ty
embedPrimFun (PrimQuot               ty) = embedQuot ty
embedPrimFun (PrimRem                ty) = embedRem ty
embedPrimFun (PrimQuotRem            ty) = embedQuotRem ty
embedPrimFun (PrimIDiv               ty) = embedIDiv ty
embedPrimFun (PrimMod                ty) = embedMod ty
embedPrimFun (PrimDivMod             ty) = embedDivMod ty
embedPrimFun (PrimBAnd               ty) = embedBAnd ty
embedPrimFun (PrimBOr                ty) = embedBOr ty
embedPrimFun (PrimBXor               ty) = embedBXor ty
embedPrimFun (PrimBNot               ty) = embedBNot ty
embedPrimFun (PrimBShiftL            ty) = embedBShiftL ty
embedPrimFun (PrimBShiftR            ty) = embedBShiftR ty
embedPrimFun (PrimBRotateL           ty) = embedBRotateL ty
embedPrimFun (PrimBRotateR           ty) = embedBRotateR ty
embedPrimFun (PrimPopCount           ty) = embedPopCount ty
embedPrimFun (PrimCountLeadingZeros  ty) = embedCountLeadingZeros ty
embedPrimFun (PrimCountTrailingZeros ty) = embedCountTrailingZeros ty
embedPrimFun (PrimFDiv               ty) = embedFDiv ty
embedPrimFun (PrimRecip              ty) = embedRecip ty
embedPrimFun (PrimSin                ty) = embedSin ty
embedPrimFun (PrimCos                ty) = embedCos ty
embedPrimFun (PrimTan                ty) = embedTan ty
embedPrimFun (PrimAsin               ty) = embedAsin ty
embedPrimFun (PrimAcos               ty) = embedAcos ty
embedPrimFun (PrimAtan               ty) = embedAtan ty
embedPrimFun (PrimSinh               ty) = embedSinh ty
embedPrimFun (PrimCosh               ty) = embedCosh ty
embedPrimFun (PrimTanh               ty) = embedTanh ty
embedPrimFun (PrimAsinh              ty) = embedAsinh ty
embedPrimFun (PrimAcosh              ty) = embedAcosh ty
embedPrimFun (PrimAtanh              ty) = embedAtanh ty
embedPrimFun (PrimExpFloating        ty) = embedExpFloating ty
embedPrimFun (PrimSqrt               ty) = embedSqrt ty
embedPrimFun (PrimLog                ty) = embedLog ty
embedPrimFun (PrimFPow               ty) = embedFPow ty
embedPrimFun (PrimLogBase            ty) = embedLogBase ty
embedPrimFun (PrimTruncate        ta tb) = embedTruncate ta tb
embedPrimFun (PrimRound           ta tb) = embedRound ta tb
embedPrimFun (PrimFloor           ta tb) = embedFloor ta tb
embedPrimFun (PrimCeiling         ta tb) = embedCeiling ta tb
embedPrimFun (PrimAtan2              ty) = embedAtan2 ty
embedPrimFun (PrimIsNaN              ty) = embedIsNaN ty
embedPrimFun (PrimIsInfinite         ty) = embedIsInfinite ty
embedPrimFun (PrimLt                 ty) = embedLt ty
embedPrimFun (PrimGt                 ty) = embedGt ty
embedPrimFun (PrimLtEq               ty) = embedLtEq ty
embedPrimFun (PrimGtEq               ty) = embedGtEq ty
embedPrimFun (PrimEq                 ty) = embedEq ty
embedPrimFun (PrimNEq                ty) = embedNEq ty
embedPrimFun (PrimMax                ty) = embedMax ty
embedPrimFun (PrimMin                ty) = embedMin ty
embedPrimFun PrimLAnd                    = embedLAnd
embedPrimFun PrimLOr                     = embedLOr
embedPrimFun PrimLNot                    = embedLNot
embedPrimFun PrimOrd                     = embedOrd
embedPrimFun PrimChr                     = embedChr
embedPrimFun PrimBoolToInt               = embedBoolToInt
embedPrimFun (PrimFromIntegral ta tb)    = embedFromIntegral ta tb
embedPrimFun (PrimToFloating ta tb)      = embedToFloating ta tb


embedAdd :: NumType a -> TExpQ (a,a) -> TExpQ a
embedAdd (IntegralNumType t) | IntegralDict <- integralDict t = uncurry [|| (+) ||]
embedAdd (FloatingNumType t) | FloatingDict <- floatingDict t = uncurry [|| (+) ||]

embedSub :: NumType a -> TExpQ (a,a) -> TExpQ a
embedSub (IntegralNumType ty) | IntegralDict <- integralDict ty = uncurry [|| (-) ||]
embedSub (FloatingNumType ty) | FloatingDict <- floatingDict ty = uncurry [|| (-) ||]

embedMul :: NumType a -> TExpQ (a,a) -> TExpQ a
embedMul (IntegralNumType ty) | IntegralDict <- integralDict ty = uncurry [|| (*) ||]
embedMul (FloatingNumType ty) | FloatingDict <- floatingDict ty = uncurry [|| (*) ||]

embedNeg :: NumType a -> TExpQ a -> TExpQ a
embedNeg (IntegralNumType ty) x | IntegralDict <- integralDict ty = [|| negate $$x ||]
embedNeg (FloatingNumType ty) x | FloatingDict <- floatingDict ty = [|| negate $$x ||]

embedAbs :: NumType a -> TExpQ a -> TExpQ a
embedAbs (IntegralNumType ty) x | IntegralDict <- integralDict ty = [|| abs $$x ||]
embedAbs (FloatingNumType ty) x | FloatingDict <- floatingDict ty = [|| abs $$x ||]

embedSig :: NumType a -> TExpQ a -> TExpQ a
embedSig (IntegralNumType ty) x | IntegralDict <- integralDict ty = [|| signum $$x ||]
embedSig (FloatingNumType ty) x | FloatingDict <- floatingDict ty = [|| signum $$x ||]

embedQuot :: IntegralType a -> TExpQ (a,a) -> TExpQ a
embedQuot ty | IntegralDict <- integralDict ty = uncurry [|| quot ||]

embedRem :: IntegralType a -> TExpQ (a,a) -> TExpQ a
embedRem ty | IntegralDict <- integralDict ty = uncurry [|| rem ||]

embedQuotRem :: IntegralType a -> TExpQ (a,a) -> TExpQ (a,a)
embedQuotRem ty | IntegralDict <- integralDict ty = uncurry [|| quotRem ||]

embedIDiv :: IntegralType a -> TExpQ (a,a) -> TExpQ a
embedIDiv ty | IntegralDict <- integralDict ty = uncurry [|| div ||]

embedMod :: IntegralType a -> TExpQ (a,a) -> TExpQ a
embedMod ty | IntegralDict <- integralDict ty = uncurry [|| mod ||]

embedDivMod :: IntegralType a -> TExpQ (a,a) -> TExpQ (a,a)
embedDivMod ty | IntegralDict <- integralDict ty = uncurry [|| divMod ||]

embedBAnd :: IntegralType a -> TExpQ (a,a) -> TExpQ a
embedBAnd ty | IntegralDict <- integralDict ty = uncurry [|| (.&.) ||]

embedBOr :: IntegralType a -> TExpQ (a,a) -> TExpQ a
embedBOr ty | IntegralDict <- integralDict ty = uncurry [|| (.|.) ||]

embedBXor :: IntegralType a -> TExpQ (a,a) -> TExpQ a
embedBXor ty | IntegralDict <- integralDict ty = uncurry [|| xor ||]

embedBNot :: IntegralType a -> TExpQ a -> TExpQ a
embedBNot ty x | IntegralDict <- integralDict ty = [|| complement $$x ||]

embedBShiftL :: IntegralType a -> TExpQ (a, Int) -> TExpQ a
embedBShiftL ty | IntegralDict <- integralDict ty = uncurry [|| shiftL ||]

embedBShiftR :: IntegralType a -> TExpQ (a, Int) -> TExpQ a
embedBShiftR ty | IntegralDict <- integralDict ty = uncurry [|| shiftR ||]

embedBRotateL :: IntegralType a -> TExpQ (a, Int) -> TExpQ a
embedBRotateL ty | IntegralDict <- integralDict ty = uncurry [|| rotateL ||]

embedBRotateR :: IntegralType a -> TExpQ (a, Int) -> TExpQ a
embedBRotateR ty | IntegralDict <- integralDict ty = uncurry [|| rotateR ||]

embedPopCount :: IntegralType a -> TExpQ a -> TExpQ Int
embedPopCount ty x | IntegralDict <- integralDict ty = [|| popCount $$x ||]

embedCountLeadingZeros :: IntegralType a -> TExpQ a -> TExpQ Int
embedCountLeadingZeros ty x | IntegralDict <- integralDict ty = [|| countLeadingZeros $$x ||]

embedCountTrailingZeros :: IntegralType a -> TExpQ a -> TExpQ Int
embedCountTrailingZeros ty x | IntegralDict <- integralDict ty = [|| countTrailingZeros $$x ||]


embedFDiv :: FloatingType a -> TExpQ (a,a) -> TExpQ a
embedFDiv ty | FloatingDict <- floatingDict ty = uncurry [|| (/) ||]

embedRecip :: FloatingType a -> TExpQ a -> TExpQ a
embedRecip ty x | FloatingDict <- floatingDict ty = [|| recip $$x ||]

embedSin :: FloatingType a -> TExpQ a -> TExpQ a
embedSin ty x | FloatingDict <- floatingDict ty = [|| sin $$x ||]

embedCos :: FloatingType a -> TExpQ a -> TExpQ a
embedCos ty x | FloatingDict <- floatingDict ty = [|| cos $$x ||]

embedTan :: FloatingType a -> TExpQ a -> TExpQ a
embedTan ty x | FloatingDict <- floatingDict ty = [|| tan $$x ||]

embedAsin :: FloatingType a -> TExpQ a -> TExpQ a
embedAsin ty x | FloatingDict <- floatingDict ty = [|| asin $$x ||]

embedAcos :: FloatingType a -> TExpQ a -> TExpQ a
embedAcos ty x | FloatingDict <- floatingDict ty = [|| acos $$x ||]

embedAtan :: FloatingType a -> TExpQ a -> TExpQ a
embedAtan ty x | FloatingDict <- floatingDict ty = [|| atan $$x ||]

embedSinh :: FloatingType a -> TExpQ a -> TExpQ a
embedSinh ty x | FloatingDict <- floatingDict ty = [|| sinh $$x ||]

embedCosh :: FloatingType a -> TExpQ a -> TExpQ a
embedCosh ty x | FloatingDict <- floatingDict ty = [|| cosh $$x ||]

embedTanh :: FloatingType a -> TExpQ a -> TExpQ a
embedTanh ty x | FloatingDict <- floatingDict ty = [|| tanh $$x ||]

embedAsinh :: FloatingType a -> TExpQ a -> TExpQ a
embedAsinh ty x | FloatingDict <- floatingDict ty = [|| asinh $$x ||]

embedAcosh :: FloatingType a -> TExpQ a -> TExpQ a
embedAcosh ty x | FloatingDict <- floatingDict ty = [|| acosh $$x ||]

embedAtanh :: FloatingType a -> TExpQ a -> TExpQ a
embedAtanh ty x | FloatingDict <- floatingDict ty = [|| atanh $$x ||]

embedExpFloating :: FloatingType a -> TExpQ a -> TExpQ a
embedExpFloating ty x | FloatingDict <- floatingDict ty = [|| P.exp $$x ||]

embedSqrt :: FloatingType a -> TExpQ a -> TExpQ a
embedSqrt ty x | FloatingDict <- floatingDict ty = [|| sqrt $$x ||]

embedLog :: FloatingType a -> TExpQ a -> TExpQ a
embedLog ty x | FloatingDict <- floatingDict ty = [|| log $$x ||]

embedFPow :: FloatingType a -> TExpQ (a,a) -> TExpQ a
embedFPow ty | FloatingDict <- floatingDict ty = uncurry [|| (**) ||]

embedLogBase :: FloatingType a -> TExpQ (a,a) -> TExpQ a
embedLogBase ty | FloatingDict <- floatingDict ty = uncurry [|| logBase ||]

embedTruncate :: FloatingType a -> IntegralType b -> TExpQ a -> TExpQ b
embedTruncate ta tb x
  | FloatingDict <- floatingDict ta
  , IntegralDict <- integralDict tb
  = [|| truncate $$x ||]

embedRound :: FloatingType a -> IntegralType b -> TExpQ a -> TExpQ b
embedRound ta tb x
  | FloatingDict <- floatingDict ta
  , IntegralDict <- integralDict tb
  = [|| round $$x ||]

embedFloor :: FloatingType a -> IntegralType b -> TExpQ a -> TExpQ b
embedFloor ta tb x
  | FloatingDict <- floatingDict ta
  , IntegralDict <- integralDict tb
  = [|| floor $$x ||]

embedCeiling :: FloatingType a -> IntegralType b -> TExpQ a -> TExpQ b
embedCeiling ta tb x
  | FloatingDict <- floatingDict ta
  , IntegralDict <- integralDict tb
  = [|| ceiling $$x ||]

embedAtan2 :: FloatingType a -> TExpQ (a,a) -> TExpQ a
embedAtan2 ty | FloatingDict <- floatingDict ty = uncurry [|| atan2 ||]

embedIsNaN :: FloatingType a -> TExpQ a -> TExpQ Bool
embedIsNaN ty x | FloatingDict <- floatingDict ty = [|| isNaN $$x ||]

embedIsInfinite :: FloatingType a -> TExpQ a -> TExpQ Bool
embedIsInfinite ty x | FloatingDict <- floatingDict ty = [|| isInfinite $$x ||]

embedLt :: SingleType a -> TExpQ (a,a) -> TExpQ Bool
embedLt (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry [|| (<) ||]
embedLt (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry [|| (<) ||]
embedLt (NonNumSingleType ty)                | NonNumDict   <- nonNumDict ty   = uncurry [|| (<) ||]

embedGt :: SingleType a -> TExpQ (a,a) -> TExpQ Bool
embedGt (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry [|| (>) ||]
embedGt (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry [|| (>) ||]
embedGt (NonNumSingleType ty)                | NonNumDict   <- nonNumDict ty   = uncurry [|| (>) ||]

embedLtEq :: SingleType a -> TExpQ (a,a) -> TExpQ Bool
embedLtEq (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry [|| (<=) ||]
embedLtEq (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry [|| (<=) ||]
embedLtEq (NonNumSingleType ty)                | NonNumDict   <- nonNumDict ty   = uncurry [|| (<=) ||]

embedGtEq :: SingleType a -> TExpQ (a,a) -> TExpQ Bool
embedGtEq (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry [|| (>=) ||]
embedGtEq (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry [|| (>=) ||]
embedGtEq (NonNumSingleType ty)                | NonNumDict   <- nonNumDict ty   = uncurry [|| (>=) ||]

embedEq :: SingleType a -> TExpQ (a,a) -> TExpQ Bool
embedEq (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry [|| (==) ||]
embedEq (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry [|| (==) ||]
embedEq (NonNumSingleType ty)                | NonNumDict   <- nonNumDict ty   = uncurry [|| (==) ||]

embedNEq :: SingleType a -> TExpQ (a,a) -> TExpQ Bool
embedNEq (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry [|| (/=) ||]
embedNEq (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry [|| (/=) ||]
embedNEq (NonNumSingleType ty)                | NonNumDict   <- nonNumDict ty   = uncurry [|| (/=) ||]

embedMax :: SingleType a -> TExpQ (a,a) -> TExpQ a
embedMax (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry [|| max ||]
embedMax (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry [|| max ||]
embedMax (NonNumSingleType ty)                | NonNumDict   <- nonNumDict ty   = uncurry [|| max ||]

embedMin :: SingleType a -> TExpQ (a,a) -> TExpQ a
embedMin (NumSingleType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry [|| min ||]
embedMin (NumSingleType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry [|| min ||]
embedMin (NonNumSingleType ty)                | NonNumDict   <- nonNumDict ty   = uncurry [|| min ||]

embedLAnd :: TExpQ (Bool, Bool) -> TExpQ Bool
embedLAnd = uncurry [|| (&&) ||]

embedLOr  :: TExpQ (Bool, Bool) -> TExpQ Bool
embedLOr = uncurry [|| (||) ||]

embedLNot :: TExpQ Bool -> TExpQ Bool
embedLNot x = [|| not $$x ||]

embedOrd :: TExpQ Char -> TExpQ Int
embedOrd x = [|| ord $$x ||]

embedChr :: TExpQ Int -> TExpQ Char
embedChr x = [|| chr $$x ||]

embedBoolToInt :: TExpQ Bool -> TExpQ Int
embedBoolToInt x = [|| case $$x of
                         True  -> 1
                         False -> 0 ||]

embedFromIntegral :: IntegralType a -> NumType b -> TExpQ a -> TExpQ b
embedFromIntegral ta (IntegralNumType tb) x
  | IntegralDict <- integralDict ta
  , IntegralDict <- integralDict tb
  = [|| fromIntegral $$x ||]

embedFromIntegral ta (FloatingNumType tb) x
  | IntegralDict <- integralDict ta
  , FloatingDict <- floatingDict tb
  = [|| fromIntegral $$x ||]

embedToFloating :: NumType a -> FloatingType b -> TExpQ a -> TExpQ b
embedToFloating (IntegralNumType ta) tb x
  | IntegralDict <- integralDict ta
  , FloatingDict <- floatingDict tb
  = [|| realToFrac $$x ||]

embedToFloating (FloatingNumType ta) tb x
  | FloatingDict <- floatingDict ta
  , FloatingDict <- floatingDict tb
  = [|| realToFrac $$x ||]


-- Utilities
-- ---------

uncurry :: TExpQ (a -> b -> c) -> TExpQ (a,b) -> TExpQ c
uncurry f x = [|| case $$x of { (a,b) -> $$f a b } ||]

