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
-- Contexts & Environments
------------------------------------------------------------------------------

data Context :: Bwd Kind -> * where
  C0 :: Context B0
  (:\) :: Sorted gamma =>
          Context gamma -> (String , Info k ^ gamma) ->
          Context (gamma :< k)

data Info (k :: Kind)(gamma :: Bwd Kind) :: * where
  SynI :: Term TTOb (Obj Chk) gamma -> Info (Obj Syn) gamma
  ChkI :: Info (Obj Chk) gamma
  PntI :: Info (Obj Pnt) gamma
  (:=>>) :: Info j gamma -> Info k (gamma :< j) -> Info (j :->> k) gamma

infixr 5 :=>>

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
    => Context delta
    -> PreInfo l k delta
    -> Term l k gamma
    -> Select gamma theta ^ delta
    -> ALL (Radical delta) theta
    -> Radical delta k
sub _ (ChkPI (_T :^ _)) _ _ _ | isDull _T = (Ob Dull :^ oN) ::: (ChkI :^ oN)

isDull :: Term TTOb (Obj Chk) gamma -> Bool
isDull One = True
isDull (Pi (Pair c _ (L x _T))) = isDull _T
isDull (Pi (Pair c _ (K _T))) = isDull _T
isDull _                  = False


