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

type family ComputeSort (s :: Sort) :: Sort where
  ComputeSort Syn = Chk
  ComputeSort Pnt = Pnt
  ComputeSort Chk = Chk

------------------------------------------------------------------------------
-- Framework Kinds
------------------------------------------------------------------------------

data Kind = Obj Sort | Kind :->> Kind

infixr 5 :->>

type family ComputeKind (k :: Kind) :: Kind where
  ComputeKind (Obj s) = Obj (ComputeSort s)
  ComputeKind (j :->> k) = j :->> ComputeKind k

data Status = Meta | TTOb

------------------------------------------------------------------------------
-- Terms (in normal form)
------------------------------------------------------------------------------

data Term :: Status -> Kind -> (Bwd Kind -> *) where
  Abs :: (j !- Term Meta k) gamma -> Term Meta (j :->> k) gamma
  Ob :: Term TTOb (Obj s) gamma -> Term Meta (Obj s) gamma
  Inst :: (Term TTOb (j :->> k) >< Term Meta (ComputeKind j)) gamma ->
          Term TTOb k gamma
  
  V :: Term TTOb k (B0 :< k)

  E :: Term TTOb (Obj Syn) gamma -> Term TTOb (Obj Chk) gamma

  Star :: Term TTOb (Obj Chk) B0

  Pi :: (Term TTOb (Obj Chk)  ><  (Obj Syn) !- Term TTOb (Obj Chk)) gamma ->
        Term TTOb (Obj Chk) gamma
  Lam :: ((Obj Syn) !- Term TTOb (Obj Chk)) gamma -> Term TTOb (Obj Chk) gamma
  -- this could be Term Meta (Obj Syn :->> Obj Chk)
  App :: (Term TTOb (Obj Syn) >< Term TTOb (Obj Chk)) gamma ->
         Term TTOb (Obj Syn) gamma

  One :: Term TTOb (Obj Chk) B0
  Dull :: Term TTOb (Obj Chk) B0

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

data Info (k :: Kind)(gamma :: Bwd Kind) :: * where
  SynI :: Term TTOb (Obj Chk) gamma -> Info (Obj Syn) gamma
  ChkI :: Info (Obj Chk) gamma
  PntI :: Info (Obj Pnt) gamma
  (:=>>) :: Info j gamma -> Info k (gamma :< j) -> Info (j :->> k) gamma

infixr 5 :=>>

-- a term with enough info to compute
data Radical :: Bwd Kind -> Kind -> * where
  (:::) :: Term Meta (ComputeKind k) ^ gamma -> Info k ^ gamma ->
           Radical gamma k


------------------------------------------------------------------------------
-- Substitution is hereditary 
------------------------------------------------------------------------------

data PreInfo (s :: Status)(k :: Kind)(gamma :: Bwd Kind) :: * where
  (:~>>) :: Info j ^ gamma -> PreInfo Meta k (gamma :< j) ->
    PreInfo Meta (j :->> k) gamma
  HedPI :: PreInfo TTOb (j :->> k) gamma
  ChkPI :: Term TTOb (Obj Chk) ^ gamma -> PreInfo l (Obj Chk) gamma
  SynPI :: PreInfo l (Obj Syn) gamma
  PntPI :: PreInfo l (Obj Pnt) gamma
  
sub :: Sorted delta
    => Context delta -- target context
    -> PreInfo l k delta -- information known in advance about target term
    -> Term l k gamma -- term in which we are substituting
    -> Select gamma theta ^ delta -- subs for theta<=gamma, embed rest in delta
    -> ALL (Radical delta) theta -- radicals over delta for every var in theta
    -> Radical delta k 
sub _ (ChkPI (_T :^ _)) _ _ _ | isDull _T = (Ob Dull :^ oN) ::: (ChkI :^ oN)
sub delta SynPI V (Hit None :^ _) (AS A0 rad) = rad
sub delta SynPI V (Miss None :^ r) A0 =
  (Ob (E V) :^ r) ::: snd (lookupC r delta)
sub delta _ (Inst (Pair c f s)) xz radz =
  missDiscard c xz radz $ \ xzf radzf xzs radzs ->
  case sub delta HedPI f xzf radzf of
    ((Abs t :^ r) ::: ((j :=>> k) :^ r')) -> --(t :^ r) ::: k :^ 
      case sub delta (preCook j r') s xzs radzs of
        rads -> sortedObj r' $
          undefined ::: subInfo delta k (Hit misser :^ r') (AS A0 _)
          -- need to think more carefully about defs of info, radical, etc.
subInfo :: Sorted delta
        => Context delta
        -> Info k gamma
        -> Select gamma theta ^ delta
        -> ALL (Radical delta) theta
        -> Info k ^ delta
subInfo delta (SynI _T) xz radz = undefined

preCook :: Info j gamma -> gamma <= delta -> PreInfo Meta (ComputeKind j) delta
preCook (SynI _T) r = ChkPI (_T :^ r)
preCook ChkI _ = undefined -- FIXME impossible because no bindings of chk
preCook PntI _ = PntPI
preCook (j :=>> k) r = (j :^ r) :~>> preCook k (OS r)

isDull :: Term TTOb (Obj Chk) gamma -> Bool
isDull One = True
isDull (Pi (Pair c _ (L x _T))) = isDull _T
isDull (Pi (Pair c _ (K _T))) = isDull _T
isDull _ = False


