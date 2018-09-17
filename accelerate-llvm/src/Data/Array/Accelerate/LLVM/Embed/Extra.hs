{-# LANGUAGE RoleAnnotations     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_HADDOCK hide #-}
-- |
-- Module      : Data.Array.Accelerate.LLVM.Embed.Extra
-- Copyright   : [2014..2018] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.LLVM.Embed.Extra (

  module Data.Array.Accelerate.LLVM.Embed.Extra,

  TH.letS,
  TH.valD,
  TH.unsafeTExpCoerce,

) where

import Data.Typeable
import Language.Haskell.TH                                          ( Q )
import qualified Language.Haskell.TH                                as TH
import qualified Language.Haskell.TH.Syntax                         as TH


type TExpQ a = Q (TH.TExp a)


-- | Abstract type representing names in the syntax tree
--
type role TName nominal                       -- as with TExp
newtype TName a = TName { unTName :: TH.Name }


-- | Generate a captureable name. Occurrences of such names will be resolved
-- according to the Haskell scoping rules at the occurrence site.
--
mkTName :: String -> TName a
mkTName = TName . TH.mkName

-- | Generate a fresh name, which can not be captured.
--
newTName :: String -> Q (TName a)
newTName str = TName <$> TH.newName str


varE :: TName a -> TExpQ a
varE (TName n) = return (TH.TExp (TH.VarE n))

varP :: TName a -> TH.PatQ
varP (TName n) = TH.varP n

letE :: [TH.DecQ] -> TExpQ a -> TExpQ a
letE ds e = TH.unsafeTExpCoerce $ TH.letE ds (TH.unTypeQ e)

doE :: [TH.StmtQ] -> TH.TExpQ a
doE ss = TH.unsafeTExpCoerce (TH.doE ss)

bindS :: TH.PatQ -> TExpQ b -> TH.StmtQ
bindS p e = TH.bindS p (TH.unTypeQ e)

noBindS :: TExpQ a -> TH.StmtQ
noBindS e = TH.noBindS (TH.unTypeQ e)

normalB :: TExpQ a -> TH.BodyQ
normalB e = TH.normalB (TH.unTypeQ e)


withSigE :: forall e. Typeable e => TExpQ e -> TExpQ e
withSigE e = e `sigE` typeRepToType (typeOf (undefined::e))

sigE :: TExpQ t -> Q TH.Type -> TExpQ t
sigE e t = TH.unsafeTExpCoerce $ TH.sigE (TH.unTypeQ e) t

typeRepToType :: TypeRep -> Q TH.Type
typeRepToType trep = do
  let (con, args)     = splitTyConApp trep
      name            = TH.Name (TH.OccName (tyConName con)) (TH.NameG TH.TcClsName (TH.PkgName (tyConPackage con)) (TH.ModName (tyConModule con)))
      --
      appsT x []      = x
      appsT x (y:xs)  = appsT (TH.AppT x y) xs
      --
  resultArgs <- mapM typeRepToType args
  return (appsT (TH.ConT name) resultArgs)

