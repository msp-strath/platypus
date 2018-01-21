module Tm where

open import OPE
open import Datoid
open import Syntax

data Sort : Set where
  chk syn poi : Sort

KI = Kind Sort
CX = Cx Sort

data TAG : Sort -> Set where
  TYPE PI LA SG PR UN VD PAT PAV EM : TAG chk
  AP FST SND PAP PAX AN : TAG syn
  P0 P1 MUX : TAG poi

SORT : Sort -> Datoid
Data (SORT i) = TAG i
decide (SORT chk) TYPE TYPE = yes refl
decide (SORT chk) PI PI = yes refl
decide (SORT chk) LA LA = yes refl
decide (SORT chk) SG SG = yes refl
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

SYNTAX : Sort -> Desc Sort
SYNTAX i = SORT i %' \
  { TYPE -> One'
  ; PI   -> rec' ([] => chk) *' rec' body
  ; LA   -> rec' body
  ; SG   -> rec' ([] => chk) *' rec' body
  ; PR   -> rec' ([] => chk) *' rec' ([] => chk)
  ; UN   -> One'
  ; VD   -> One'
  ; PAT  -> rec' line *' (rec' ([] => chk) *' rec' ([] => chk))
  ; PAV  -> rec' line
  ; EM   -> rec' ([] => syn)
  ; AP   -> rec' ([] => syn) *' rec' ([] => chk)
  ; FST  -> rec' ([] => syn)
  ; SND  -> rec' ([] => syn)
  ; PAP  -> rec' ([] => syn) *' rec' ([] => poi)
  ; PAX  -> rec' line *' rec' ([] => chk)
  ; AN   -> rec' ([] => chk) *' rec' ([] => chk)
  ; P0   -> One'
  ; P1   -> One'
  ; MUX  -> rec' ([] => poi) *' (rec' ([] => poi) *' rec' ([] => poi))
  }
