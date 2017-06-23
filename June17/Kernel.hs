--------------------------------------------------------------------------------
{-# LANGUAGE GADTs, DataKinds, TypeOperators, KindSignatures,
             ConstraintKinds, RankNTypes, FlexibleInstances,
             TypeFamilies, StandaloneDeriving, DeriveFoldable,
             DeriveFunctor, DeriveTraversable, FlexibleContexts,
             GeneralizedNewtypeDeriving #-}
module Kernel where

import Data.List
import Prelude hiding ((^^))
import Data.Void
import Data.Type.Equality((:~:)(Refl))
import Control.Monad
import Control.Newtype
import Data.Monoid

import Utils
import OPE

------------------------------------------------------------------------------
-- Syntactic Sorts
------------------------------------------------------------------------------

data Sort = Chk | Syn | Pnt

data DualSort (s :: Sort)(s' :: Sort) :: * where
  DualSyn :: DualSort Syn Chk
  DualPnt :: DualSort Pnt Pnt
  DualChk :: DualSort Chk Syn

symSort :: DualSort s0 s1 -> DualSort s1 s0
symSort DualSyn = DualChk
symSort DualChk = DualSyn
symSort DualPnt = DualPnt

funSort :: DualSort s0 s1 -> DualSort s0 s2 -> Holds (s1 ~ s2)
funSort DualSyn DualSyn t = t
funSort DualChk DualChk t = t
funSort DualPnt DualPnt t = t

{-
test :: DualSort s ~ DualSort t => Term Neut (Obj s) B0 -> Term Neut (Obj t) B0
test x = x
-}

------------------------------------------------------------------------------
-- Framework Kinds
------------------------------------------------------------------------------

data Kind = Obj Sort | Kind :->> Kind

infixr 5 :->>

data DualKind (k :: Kind) (k' :: Kind) :: * where
  DualObj :: DualSort s s' -> DualKind (Obj s) (Obj s')
  DualArr :: DualKind j j' -> DualKind k k' -> DualKind (j :->> k) (j' :->> k')

symKind :: DualKind k0 k1 -> DualKind k1 k0
symKind (DualObj s) = DualObj (symSort s)
symKind (DualArr s0 s1) = DualArr (symKind s0) (symKind s1)

funKind :: DualKind k0 k1 -> DualKind k0 k2 -> Holds (k1 ~ k2)
funKind (DualObj s0) (DualObj s1) t = funSort s0 s1 t
funKind (DualArr s0 s0') (DualArr s1 s1') t =
  funKind s0 s1 $ funKind s0' s1' $ t

data Status = Norm | Neut

------------------------------------------------------------------------------
-- Terms (in normal form)
------------------------------------------------------------------------------

data Term :: Status -> Kind -> (Bwd Kind -> *) where
  Abs :: (j !- Term Norm k) gamma -> Term Norm (j :->> k) gamma
  Ob :: Term Neut (Obj s) gamma -> Term Norm (Obj s) gamma
  Inst :: (Term Neut (j :->> k) >< Term Norm j) gamma ->
          Term Neut k gamma
  
  V :: Term Neut k (B0 :< k)

  E :: Term Neut (Obj Syn) gamma -> Term Neut (Obj Chk) gamma

  Star :: Term Neut (Obj Chk) B0

  Pi :: (Term Neut (Obj Chk)  ><  (Obj Syn) !- Term Neut (Obj Chk)) gamma ->
        Term Neut (Obj Chk) gamma
  Lam :: ((Obj Syn) !- Term Neut (Obj Chk)) gamma -> Term Neut (Obj Chk) gamma
  -- this could be Term Norm (Obj Syn :->> Obj Chk)
  App :: (Term Neut (Obj Syn) >< Term Neut (Obj Chk)) gamma ->
         Term Neut (Obj Syn) gamma

  One :: Term Neut (Obj Chk) B0
  Dull :: Term Neut (Obj Chk) B0

------------------------------------------------------------------------------
-- Contexts
------------------------------------------------------------------------------

data Context :: Bwd Kind -> * where
  C0 :: Context B0
  (:\) :: Sorted gamma =>
          Context gamma -> (String , Info k ^ gamma) ->
          Context (gamma :< k)

lookupC :: (B0 :< k) <= delta -> Context delta -> (String , Info k ^ delta)
lookupC (OS r) (delta :\ (x, i :^ r')) = (x,i :^ O' r')
lookupC (O' r) (delta :\ _) = case lookupC r delta of
  (x, i :^ r') -> (x,i :^ O' r')

-- what you put in the context for a variable of kind k
data Info (k :: Kind)(gamma :: Bwd Kind) :: * where
  SynI :: Term Neut (Obj Chk) gamma -> Info (Obj Syn) gamma
  PntI :: Info (Obj Pnt) gamma
  ArrI :: DualKind j j' -> Info j' gamma -> Info k (gamma :< j') ->
    Info (j :->> k) gamma

-- what you put in an environment for a variable of kind k
data Radical :: Bwd Kind -> Kind -> * where
  Rad :: DualKind k k' -> Term Norm k' ^ gamma -> Info k ^ gamma ->
           Radical gamma k


------------------------------------------------------------------------------
-- Substitution is hereditary 
------------------------------------------------------------------------------

data PreSub (s :: Status)(k :: Kind)(gamma :: Bwd Kind) :: * where
  ArrPre :: Info j ^ gamma -> PreSub Norm k (gamma :< j) ->
    PreSub Norm (j :->> k) gamma
  HedPre :: PreSub Neut (j :->> k) gamma
  ChkPre :: Term Neut (Obj Chk) ^ gamma -> PreSub s (Obj Chk) gamma
  SynPre :: PreSub s (Obj Syn) gamma
  PntPre :: PreSub s (Obj Pnt) gamma

data PostSub (s :: Status)(k :: Kind)(gamma :: Bwd Kind) :: * where
  SynPost :: Radical delta (Obj Syn) -> PostSub s (Obj Syn) delta
  ChkPost :: Term Neut (Obj Chk) ^ delta -> PostSub s (Obj Chk) delta
  PntPost :: Term Neut (Obj Pnt) ^ delta -> PostSub s (Obj Pnt) delta
  ArrPost :: Term Norm (j :->> k) ^ delta -> PostSub Norm (j :->> k) delta
  HedPost :: Radical delta (j :->> k) -> PostSub Neut (j :->> k) delta
  
sub :: Sorted delta
    => Context delta -- target context
    -> PreSub s k delta -- information known in advance about target term
    -> Term s k gamma -- term in which we are substituting
    -> Select gamma theta ^ delta -- subs for theta<=gamma, embed rest in delta
    -> ALL (Radical delta) theta -- radicals over delta for every var in theta
    -> PostSub s k delta
sub _ (ChkPre (_T :^ _)) _ _ _ | isDull _T = ChkPost (Dull :^ oN)
sub delta SynPre V (Hit None :^ _) (AS A0 rad) = SynPost rad
sub delta SynPre V (Miss None :^ r) A0 = SynPost $
  Rad (DualObj DualSyn) (Ob (E V) :^ r) (snd (lookupC r delta))
sub delta _ (Inst (Pair c f s)) xz radz =
  missDiscard c xz radz $ \ xzf radzf xzs radzs ->
  case sub delta HedPre f xzf radzf of
    HedPost (Rad p (Abs t :^ r) ((ArrI q j k) :^ r')) -> --(t :^ r) ::: k :^ 
      case sub delta (preCook q j r') s xzs radzs of
        rads -> sortedObj r' $ 
          undefined -- ::: subInfo delta k (Hit misser :^ r') (AS A0 _)
          -- need to think more carefully about defs of info, radical, etc.
          
subInfo :: Sorted delta
        => Context delta
        -> Info k gamma
        -> Select gamma theta ^ delta
        -> ALL (Radical delta) theta
        -> Info k ^ delta
subInfo delta (SynI _T) xz radz = undefined

preCook :: DualKind j j' -> Info j' gamma -> gamma <= delta ->
  PreSub Norm j delta
preCook (DualObj DualChk) (SynI _T) r = ChkPre (_T :^ r)
preCook (DualObj DualPnt) PntI _ = PntPre
preCook (DualArr q q') (ArrI p j k) r = funKind (symKind q) p $
  ArrPre (j :^ r) (preCook q' k (OS r))

isDull :: Term Neut (Obj Chk) gamma -> Bool
isDull One = True
isDull (Pi (Pair c _ (L x _T))) = isDull _T
isDull (Pi (Pair c _ (K _T))) = isDull _T
isDull _ = False


