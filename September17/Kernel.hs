--------------------------------------------------------------------------------
{-# LANGUAGE GADTs, DataKinds, TypeOperators, KindSignatures, TypeInType,
             TypeFamilies, ExistentialQuantification, Rank2Types, ScopedTypeVariables #-}

module Kernel where

import Data.Kind

import Utils
import OPE

data Sort = Chk | Syn | Pnt
data Kind = Adicity :=> Sort
type Adicity = [Kind]
type Scope = Bwd Kind

type family SORT (k :: Kind) :: Sort where
 SORT (_ :=> s) = s

type family ADICITY (k :: Kind) :: Adicity where
  ADICITY (ks :=> _) = ks

data Term :: Sort -> Scope -> * where
  Star :: Term Chk B0
  Pi   :: (TermK ('[] :=> Chk) >< TermK ('[ '[] :=> Syn] :=> Chk)) gamma ->
          Term Chk gamma
  Lam  :: TermK ('[ '[] :=> Syn] :=> Chk) gamma -> Term Chk gamma
  Emb  :: TermK ('[] :=> Syn) gamma -> Term Chk gamma
  (:$) :: CoP (B0 :< (ks :=> s)) gamma' gamma -> Spine ks gamma' -> Term s gamma -- meta level instantiation
  App  :: (TermK ('[] :=> Syn) >< TermK ('[] :=> Chk)) gamma -> Term Syn gamma -- object level app

data Spine :: [Kind] -> Bwd Kind -> * where
  S0 :: Spine '[] B0
  SC :: (TermK k >< Spine ks) gamma -> Spine (k:ks) gamma
  
type TermK k = Bind (ADICITY k) (Term (SORT k))

type family Bind (sc :: Adicity)(f :: Bwd Kind -> *) :: (Bwd Kind -> *)
  where
  Bind '[] f = f
  Bind (k:ks) f = k !- Bind ks f

data ContextEntry :: Kind -> Scope -> * where
  CESyn :: Term Chk ^ gamma {- type -}
        -> ContextEntry ('[] :=> Syn) gamma
  CEBind :: ContextEntry k gamma -> ContextEntry (ks :=> i) (gamma:<k) ->
            ContextEntry ((k:ks) :=> i) gamma
  -- something for Chk?
  
data Context :: Scope -> * where
  C0 :: Context B0
  CS :: Context gamma -> ContextEntry k gamma -> Context (gamma :< k) 
{-
kind and scope indexed context entries
-}
data Image :: Scope -> Kind -> * where
  ISyn :: Term Chk ^ delta -> Image delta ('[] :=> Syn)
  IBind :: Image (delta:<k) (ks :=> i) -> Image delta ((k:ks) :=> i)
  -- something for Chk?
  
data Mor (gamma :: Scope)(delta :: Scope) :: * where
  Mor :: Context gamma
      -> Context delta              
      -> Riffle rho gamma sigma 
      -> rho <= delta           
      -> ALL (Image delta) sigma
      -> Mor gamma delta

subChk :: Mor gamma delta -> Term Chk gamma -> Term Chk ^ delta -> Term Chk ^ delta
subChk = undefined

subSyn :: Mor gamma delta -> Term Syn gamma -> (Term Chk ^ delta,Term Chk ^ delta)
subSyn = undefined
-- some examples

idFun :: Term Chk B0
idFun = Lam (L "x" (Emb (CS' CZZ :$ S0)))

polyIdFunType :: Term Chk B0
polyIdFunType = Pi (Pair CZZ Star (L "X"
                  (Pi (Pair (CSS CZZ) (Emb (CS' CZZ :$ S0)) (K
                     (Emb (CS' CZZ :$ S0))
                  )))
                ))

polyIdFun = Lam (K idFun)
