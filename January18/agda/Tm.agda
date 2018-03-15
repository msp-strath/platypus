module Tm where

open import OPE
open import Datoid
open import Syntax

data Sort : Set where
  chk syn poi : Sort

KI = Kind Sort
CX = Cx Sort

data TAG : Sort -> Set where
  TYPE PI LA SIG PR UN VD PAT PAV EM : TAG chk
  AP FST SND PAP PAX AN : TAG syn
  P0 P1 MUX : TAG poi

SORT : Sort -> Datoid
Data (SORT i) = TAG i
decide (SORT chk) TYPE TYPE = yes refl
decide (SORT chk) PI PI = yes refl
decide (SORT chk) LA LA = yes refl
decide (SORT chk) SIG SIG = yes refl
decide (SORT chk) PR PR = yes refl
decide (SORT chk) UN UN = yes refl
decide (SORT chk) VD VD = yes refl
decide (SORT chk) PAT PAT = yes refl
decide (SORT chk) PAV PAV = yes refl
decide (SORT chk) EM EM = yes refl
decide (SORT syn) AP AP = yes refl
decide (SORT syn) FST FST = yes refl
decide (SORT syn) SND SND = yes refl
decide (SORT syn) PAP PAP = yes refl
decide (SORT syn) PAX PAX = yes refl
decide (SORT syn) AN AN = yes refl
decide (SORT poi) P0 P0 = yes refl
decide (SORT poi) P1 P1 = yes refl
decide (SORT poi) MUX MUX = yes refl
decide (SORT i) x y = no p where postulate p : (x == y) -> Zero

body : Kind Sort
body = ([] -, ([] => syn)) => chk

line : Kind Sort
line = ([] -, ([] => poi)) => chk

data Arity (I : Set) : Set where
  rec' : (K : Kind I) -> Arity I
  _*'_ : (D E : Arity I) -> Arity I
  One' : Arity I

arD : ∀ {I} → Arity I → Desc I
arD (rec' K) = rec' K
arD (ar *' ar₁) = arD ar *' arD ar₁
arD One' = One'

ARITIES' : ∀ {i} → TAG i → Arity Sort
ARITIES' TYPE = One'
ARITIES' PI   = rec' ([] => chk) *' rec' body
ARITIES' LA   = rec' body
ARITIES' SIG  = rec' ([] => chk) *' rec' body
ARITIES' PR   = rec' ([] => chk) *' rec' ([] => chk)
ARITIES' UN   = One'
ARITIES' VD   = One'
ARITIES' PAT  = rec' line *' (rec' ([] => chk) *' rec' ([] => chk))
ARITIES' PAV  = rec' line
ARITIES' EM   = rec' ([] => syn)
ARITIES' AP   = rec' ([] => syn) *' rec' ([] => chk)
ARITIES' FST  = rec' ([] => syn)
ARITIES' SND  = rec' ([] => syn)
ARITIES' PAP  = rec' ([] => syn) *' rec' ([] => poi)
ARITIES' PAX  = rec' line *' rec' ([] => chk)
ARITIES' AN   = rec' ([] => chk) *' rec' ([] => chk)
ARITIES' P0   = One'
ARITIES' P1   = One'
ARITIES' MUX  = rec' ([] => poi) *' (rec' ([] => poi) *' rec' ([] => poi))

ARITIES : ∀ {i} → TAG i → Desc Sort
ARITIES t = arD (ARITIES' t)

SYNTAX : Sort -> Desc Sort
SYNTAX i = SORT i %' ARITIES
{-
example0 : Tm SYNTAX exp chk ^^ []
example0 = [ PI /^ (([] !-^ [ TYPE /^ done^ ]^) ,^ {!!}) ]^
-}

example1 : DB SYNTAX exp chk []
example1 = [ PI / [ TYPE / <> ] , [ PI / [ EM / var (os oe) <> ] , [ EM / var (o' (os oe)) <> ] ] ]
