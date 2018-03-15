{-# OPTIONS --postfix-projections #-}

module Reduction where

open import Datoid
open import OPE
open import Tm
open import Syntax
open import Judge
open import Rules
open import Sum

import Syntax.DBSubst as DBS

open DBS using (appendDB)


dealBack : ∀ {iz jz kz} → Deal iz jz kz → DBS.Morph SYNTAX kz (iz ++ jz)
dealBack           dzz             = DBS.imor
dealBack {iz} {jz} (ds' {i = i} d) = DBS.casemor {jz = [] -, i} (DBS.cmor (dealBack d) (DBS.wmor (DBS.omor oinl) jz))
                                                                (DBS.cmor (DBS.omor oinr) (DBS.omor (oinl {jz = jz})))
dealBack           (d's         d) = DBS.wmor (dealBack d) _


subCExt : ∀ {iz jz dz} → DBS.Morph SYNTAX iz jz → CExt SYNTAX ExJF iz dz → CExt SYNTAX ExJF jz dz
subCExt a [] = []
subCExt a (_-,_ {iz = iz} ext (cent varJ varIp varSb varOp)) = (subCExt a ext) -,
  cent varJ varIp varSb (DBS.subD (DBS.wmor (DBS.wmor a iz) (patsDBD (spD (ExJF varJ .JForm.inputs)) varIp)) ((spD (ExJF varJ .JForm.outputs))) varOp)

subPrems : ∀ {iz iz' sz oz} → DBS.Morph SYNTAX iz iz'
           → Prems SYNTAX ExJF iz  sz (DeBr (DBK SYNTAX exp) (spD oz))
           → Prems SYNTAX ExJF iz' sz (DeBr (DBK SYNTAX exp) (spD oz))
subPrems {oz = oz'} a (return refl otz) = return refl (DBS.subD a (spD oz') otz)
subPrems a            fail             = fail
subPrems {oz = oz'} a (prem {iz = dz} x j intz {mz' = mz'} sb pz d)
  = prem {iz = dz} (subCExt a x) j (DBS.subD (DBS.wmor a dz) (spD (ExJF j .JForm.inputs)) intz) sb pz
         (subPrems {oz = oz'} (DBS.wmor (DBS.wmor a mz') (patsDBD (spD (ExJF j .JForm.outputs)) pz)) d)

module _ {I} {F : I → Desc I} where
  patsIntoExpr : ∀ {iz i} (ps : DB F pat i iz) -> DB F exp i (patsDB ps ++ iz)
  patsIntoExprD : ∀ {iz} D → (ps : DeBr (DBK F pat) D iz) → DeBr (DBK F exp) D (patsDBD D ps ++ iz)
  patsIntoExpr {iz} {i} [ x ] = [ patsIntoExprD (F i) x  ]
  patsIntoExpr (var {jz} x tz) = var (x <&= oinr) (patsIntoExprD (spD jz) tz)
  patsIntoExpr (pat {jz} x th) = var oinl (DBS.idSpine (th <&= oinr))
  patsIntoExprD {iz} (rec' (kz => k)) ps = replace (\ iz -> DB F exp k iz) (sym (assoc++ (patsDB ps) iz kz)) (patsIntoExpr ps)
  patsIntoExprD (C %' D) (c / ps) = c / patsIntoExprD (D c) ps
  patsIntoExprD {iz} (D *' E) (psl , psr) = DBS.subD (DBS.wmor (DBS.omor oinl) iz) D (patsIntoExprD D psl)
                                         , DBS.subD (DBS.wmor (DBS.omor  oinr) iz) E (patsIntoExprD E psr)
  patsIntoExprD One' ps = <>


module _ {s : _} where
    red-prems : ∀ {iz sz oz}
                → Prems SYNTAX ExJF iz sz (DeBr (DBK SYNTAX exp) (spD oz))
                → DB SYNTAX exp s (iz ++ sz)
                → Prems SYNTAX ExJF (iz ++ sz) [] (DeBr (DBK SYNTAX exp) (spD (([] -, ([] => s)) ++ oz)))
    red-prems {oz = oz'} (return refl otz) t
      = return refl (appendDB {iz = [] -, ([] => s)} {jz = oz'} (<> , t) (DBS.subD DBS.imor (spD oz') otz))
    red-prems fail t = fail
    red-prems {iz = iz} {sz = sz} {oz = oz'} (prem {iz = dz} cext (sort s') intz {sz' = sz'} (pick {jz' = jz'} [] sb vz) pz d) t =
      prem (subCExt (DBS.omor oinl) cext)
           (s' -red)
           (DBS.subD ( (DBS.wmor ((DBS.omor oinl)) dz) ) (spD (typing s' .JForm.inputs)) intz
           , DBS.sub ( (DBS.wmor ((DBS.omor oinr)) dz) ) (var (dealRight sb <&= oinl) (DBS.idSpine (vz <&= oinr))))
           []
           (appendDB {iz = ([] -, ([] => s'))} {jz = Typing.outputs s'} (<> , pat <> vz) pz)
           (subPrems {oz = (([] -, ([] => s)) ++ oz')} sigma
             (red-prems {oz = oz'}
               d
               (DBS.sub (DBS.casemor {jz = sz}
                             (DBS.omor (oinl {jz = ([] -, _)} <&= (oinl <&= oinl {jz = sz'})))
                             (DBS.cmor (dealBack sb) (DBS.casemor {jz = [] -, _}
                                                          (DBS.omor oinr)
                                                          (DBS.omor (oinr {jz = ([] -, _)} <&= (oinl <&= oinl {jz = sz'}))))))
                        t)))
     where
       sigma : DBS.Morph SYNTAX
                (((iz -, (jz' => s')) ++ patsDBD (spD (ExJF (sort s') .JForm.outputs)) pz) ++ sz')
                ((iz ++ sz) ++ patsDBD (spD (ExJF (s' -red) .JForm.outputs))
                                       (appendDB {iz = ([] -, ([] => s'))} {jz = Typing.outputs s'} (<> , pat <> vz) pz))
       sigma rewrite DBS.appendDB-++ {iz = ([] -, ([] => s'))} {jz = Typing.outputs s'} (<> , pat <> vz) pz
         = DBS.casemor {jz = sz'}
               (DBS.casemor {jz = patsDBD (spD (ExJF (sort s') .JForm.outputs)) pz}
                    (DBS.casemor {jz = [] -, _}
                         (DBS.omor (oinl {jz = sz} <&= oinl {jz = (([] -, (jz' => s')) ++ patsDBD (spD (Typing.outputs s')) pz)}))
                         (DBS.omor (oinl {jz = patsDBD (spD (Typing.outputs s')) pz} <&= oinr)))
                    (DBS.omor (oinr <&= oinr)))
               (DBS.omor (dealLeft sb <&= (oinr <&= oinl {jz = (([] -, (jz' => s')) ++ patsDBD (spD (Typing.outputs s')) pz)})))

    red-prems {oz = oz'} (prem x chk-eq x₁ [] pz d) t = red-prems {oz = oz'} d t
    red-prems {oz = oz'} (prem x poi-eq x₁ [] pz d) t = red-prems {oz = oz'} d t
    red-prems            (prem x syn-eq x₁ [] pz d) t = fail -- not possible with our rules
    red-prems            (prem x (_ -whnf) x₁ _ pz d) t = fail -- not possible like below
    red-prems            (prem x (_ -red) x₁ x₂ pz d) t = fail -- not possible because we are generating the reduction rules, could be ruled out by more complex JTag



red-rule : ∀ {s} →  Rule SYNTAX ExJF (sort s) → Rule SYNTAX ExJF (s -red)
red-rule {s} r .inpats = appendDB {iz = typing s .JForm.inputs} {jz = typing s .JForm.subjects} (r .inpats) (r .sbpats)
red-rule {s} r .sbpats = <>
red-rule {s} r .deduction with red-prems {oz = ExJF (sort s) .JForm.outputs} (r .deduction)
                                         (DBS.sub (DBS.omor (oinr <&= oinr)) (patsIntoExpr (r .sbpats .snd)))
... | d rewrite id++ (patsDB (r .sbpats .snd)) = d

idPats : (D : Arity Sort) → DeBr (DBK SYNTAX pat) (arD D) []
idPats (rec' (x => x₁)) = pat <> oi
idPats (D *' D₁) = (idPats D) , (idPats D₁)
idPats One' = <>

patSpine : ∀ {i} (t : TAG i) → DeBr (DBK SYNTAX pat) (ARITIES t) []
patSpine t = idPats (ARITIES' t)

whnf-rule-chk : TAG chk → Rule SYNTAX ExJF (chk -whnf)
whnf-rule-chk t .inpats = <> , [ t / patSpine t ]
whnf-rule-chk t .sbpats = <>
whnf-rule-chk EM .deduction =
  prem [] (syn -whnf) (<> , var (# 0) <>) [] ((<> , pat <> oi) , pat <> oi)
  (return refl ((<> , (var (# 1) <>))))
whnf-rule-chk t .deduction = return refl (<> , [ t / replace (DeBr (DBK SYNTAX exp) (ARITIES t)) (sym (id++ _)) (patsIntoExprD (ARITIES t) (patSpine t)) ] )

whnf-rule-an : Rule SYNTAX ExJF (syn -whnf)
whnf-rule-an .inpats = <> , [ AN / pat <> oi , pat <> oi ]
whnf-rule-an .sbpats = <>
whnf-rule-an .deduction =
  prem [] (chk -whnf) (<> , (var (# 1) <>)) [] (<> , pat <> oi)
  (prem [] (chk -whnf) (<> , var (# 1) <>) [] (<> , pat <> oi)
  (return refl ((<> , (var (# 1) <>)) , (var (# 0) <>))))



-- for contractions of the forms "(p : P) ● ↦ R ∋ u",
-- so excluding the ones for "t [ i.T >" I guess.
-- does not handle "p @ 0" or "p @ 1" either.
record Contraction : Set where
  field
    tag : TAG syn
    arRest : Arity Sort
    eliminating : ARITIES' tag == (rec' ([] => syn) *' arRest)
    lhsTm : DB SYNTAX pat chk []
    lhsTy : DB SYNTAX pat chk []
  lhs : DeBr (DBK SYNTAX pat) (arD (rec' ([] => syn) *' arRest)) []
  lhs = [ AN / lhsTm , lhsTy ] , idPats arRest
  field
    -- the outputs of syn -whnf
    rhs : DeBr (DBK SYNTAX exp) (spD ([] -, ([] => chk) -, ([] => chk)))
                    (patsDBD (arD (rec' ([] => syn) *' arRest)) lhs)

idPats-thmD : ∀ (D : Arity Sort){jz} → patsDBD (arD D) (idPats D) <= jz → DeBr (DBK SYNTAX exp) (arD D) jz
idPats-thmD D k = DBS.subD (DBS.omor k) (arD D) (patsIntoExprD (arD D) (idPats D))

module _ (c : Contraction) where
  module c = Contraction c

  whnf-rule-syn-stuck : Rule SYNTAX ExJF (syn -whnf)
  whnf-rule-syn-stuck .inpats = <> , [ c.tag / patSpine c.tag ]
  whnf-rule-syn-stuck .sbpats = <>
  whnf-rule-syn-stuck .deduction rewrite c.eliminating =
    prem [] (syn -whnf) (<> , var (oinl <&= oinr {iz = []}) <>) [] ((<> , [ EM / pat <> oi ]) , pat <> oi)
    (return refl ((<> , [ EM / [ c.tag / replace (let H = _ in λ ar → DeBr (DBK SYNTAX exp) (arD ar) H) (sym c.eliminating)
                                         (var (# 1) <> , idPats-thmD c.arRest ((oinr {iz = [] -, _} <&= oinr {iz = []}) <&= oinl {jz = [] -, _ -, _}))
                               ] ])
                      , var (# 0) <>))

  whnf-rule-syn : Rule SYNTAX ExJF (syn -whnf)
  whnf-rule-syn .inpats = <> , [ c.tag / patSpine c.tag ]
  whnf-rule-syn .sbpats = <>
  whnf-rule-syn .deduction rewrite c.eliminating =
    prem [] (syn -whnf) (<> , var (oinl <&= oinr {iz = []}) <>) [] ((<> , c.lhsTm) , c.lhsTy)
    (return refl (DBS.subD (DBS.casemor
                              (DBS.cmor (DBS.wmor (DBS.omor (oinr {jz = patsDB c.lhsTm})) (patsDB c.lhsTy)) (DBS.omor oinr))
                              (DBS.omor ((oinr {iz = [] -, _} <&= oinr {iz = []}) <&= oinl {jz = (([] ++ patsDB c.lhsTm) ++ patsDB c.lhsTy)})))
                           (spD ([] -, ([] => chk) -, ([] => chk)))
                           c.rhs))

private
  appRedRule : Rule SYNTAX ExJF (syn -red)
  appRedRule .inpats = <> , [ AP / pat <> oi , pat <> oi ]
  appRedRule .sbpats = <>
  appRedRule .deduction = prem [] (syn -red) (<> , var (# 1) <>) [] ((<> , (pat <> oi)) , [ PI / (pat <> oi , pat <> oi) ])
                        (prem [] (chk -red) ((<> , (var (# 1) <>)) , (var (# 3) <>)) [] (<> , pat <> oi)
                        (return refl ((<> , [ AP / (var (# 3) <>) , (var (# 0) <>) ]) , var (# 1) (<> , [ AN / (var (# 0) <>) , var (# 2) <> ]))))


  test1 : appRedRule .inpats == red-rule appRule .inpats
  test1 = refl

  test2 : appRedRule .sbpats == red-rule appRule .sbpats
  test2 = refl

  test3 : appRedRule .deduction == red-rule appRule .deduction
  test3 = refl


  pavRedRule : Rule SYNTAX ExJF (chk -red)
  pavRedRule .inpats = (<> , [ PAT / (pat <> oi) , ((pat <> oi) , (pat <> oi)) ]) , [ PAV / pat <> oi ]
  pavRedRule .sbpats = <>
  pavRedRule .deduction =
    prem ([] -, cent (sort poi) <> refl <>) (chk -red) ((<> , var (# 4) (<> , var (# 0) <>)) , (var (# 1) (<> , (var (# 0) <>)))) [] (<> , pat <> oi)
      (return refl (<> , [ PAV / var (# 1) (<> , var (# 0) <>) ]))


  test1b : pavRedRule .inpats == red-rule pavRule .inpats
  test1b = refl

  test2b : pavRedRule .sbpats == red-rule pavRule .sbpats
  test2b = refl

  test3b : pavRedRule .deduction == red-rule pavRule .deduction
  test3b = refl
