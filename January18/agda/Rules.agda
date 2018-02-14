{-# OPTIONS --postfix-projections #-}

module Rules where

open import Datoid
open import OPE
open import Tm
open import Syntax
open import Judge
import Agda.Builtin.Reflection as R
open import Agda.Builtin.Nat using (Nat; suc; zero)
import Agda.Builtin.List as L

-----------------------------------------------------------
-- Maybe move back into Tm/Syntax
v0 : {I : Set} -> {i : I} -> {iz : Bwd I} → The i (iz -, i)
v0 = os oe

pattern Pax t u = [ PAX  / (t , u) ]
pattern Type    = [ TYPE / <>      ]
pattern `0      = [ P0   / <>      ]
pattern `1      = [ P1   / <>      ]

var2deal : ∀ {I} {i : I} {jz} → The i jz → Sg _ \ jz' → Deal jz' ([] -, i) jz
var2deal (os x) = _ , (d's (dealL _))
var2deal (o' x) = _ , (ds' (var2deal x .snd))

``_ : ∀ {I} {i : I} {jz} → (x : The i jz) → Deal (var2deal x .fst) ([] -, i) jz
`` x = var2deal x .snd


macro
  # : Nat → R.Term → R.TC _
  # n m = R.unify m (toVar n)
     where
       argN argI : R.Term → R.Arg R.Term
       argN = R.arg (R.arg-info R.visible R.relevant)
       argI = R.arg (R.arg-info R.hidden  R.relevant)

       toVar : Nat → R.Term
       toVar zero    = R.def (quote v0) (argI R.unknown L.∷ argI R.unknown L.∷ argI R.unknown L.∷ L.[])
       toVar (suc n) = R.con (quote o') (argN (toVar n) L.∷ L.[])


-------------------------------

data JTag : Set where
  chk syn poi : JTag
  chk-eq syn-eq : JTag

ExJF : JTag -> JForm Sort
ExJF chk = ([] -, ([] => chk)) <? ([] -, ([] => chk)) ?> []
ExJF syn = []                  <? ([] -, ([] => syn)) ?> (([] -, ([] => chk)))
ExJF poi = []                  <? ([] -, ([] => poi)) ?> []
ExJF chk-eq .JForm.inputs = [] -, ([] => chk) -, ([] => chk) -, ([] => chk)
ExJF chk-eq .JForm.subjects = []
ExJF chk-eq .JForm.outputs = []
ExJF syn-eq .JForm.inputs = [] -, ([] => syn) -, ([] => syn)
ExJF syn-eq .JForm.subjects = []
ExJF syn-eq .JForm.outputs = [] -, ([] => chk)

module _ (let I = Sort) {mz sz : Cx I}{X : Cx I -> Set} where
  private
    F = SYNTAX
    JF = ExJF

  _⊢_∋_>>_ : {iz : Cx I} -> CExt F JF mz iz ->
           (let j = chk) ->
           (let open JForm (JF j)) ->
               DB F exp chk (mz ++ iz) ->
               {mz' sz' : Cx I} ->
               Subjects F JF (mz ++ iz) sz mz' sz' subjects ->
               Prems F JF ((mz ++ mz')) sz' X ->
               Prems F JF mz sz X
  G ⊢ T ∋ t >> k = prem G chk (<> , T) t <> k


  _⊢_∈_>>_ : {iz : Cx I} -> CExt F JF mz iz ->
           (let j = syn) ->
           (let open JForm (JF j)) ->
               -- DB F exp chk (mz ++ iz) ->
               {mz' sz' : Cx I} ->
               Subjects F JF (mz ++ iz) sz mz' sz' subjects ->
               (pz : DB F pat chk []) ->

               Prems F JF ((mz ++ mz') ++ patsDBD (spD outputs) (<> , pz)) sz' X ->
               Prems F JF mz sz X
  G ⊢ t ∈ T >> k = prem G syn <> t (<> , T) k

{-
lamRule : Rule SYNTAX ExJF chk
Rule.inpats lamRule = done <[ czz ]> (oz \\ [ PI / (oz \\ pat <>) <[ czz ]> (os oz \\ pat <>) ])
Rule.sbpats lamRule = done <[ czz ]> (oz \\ [ LA / (os oz \\ pat <>) ])
Rule.deduction lamRule =
  prem ([] -, cent syn done (d's dzz) ((done <[ c's czz ]> (oz \\ var (only <[ cs' czz ]> done))) ^ o' (os oz)))
    chk
    ((done <[ c's (c's czz) ]> (oz \\ var (only <[ c's (cs' czz) ]> (done <[ c's czz ]> (oz \\ var (only <[ cs' czz ]> done)))))) ^ os (os (o' oz)))
    (pick [] (d's dzz) ((done <[ c's czz ]> (oz \\ var (only <[ cs' czz ]> done))) ^ os oe))
    done
    (return refl (done ^ oe))
-}

typeRule : Rule SYNTAX ExJF chk
typeRule .inpats = <> , Type
typeRule .sbpats = <> , Type
typeRule .deduction = return refl <>

binRule : (sbpatz : DB SYNTAX pat chk [])
        → patsDBD (spD (ExJF chk .JForm.subjects)) (<> , sbpatz)
          == (([] -, ([] => chk)) -, (([] -, ([] => syn)) => chk))
        -> Rule SYNTAX ExJF chk
binRule sbpatz eq .inpats = <> , Type
binRule sbpatz eq .sbpats = <> , sbpatz
binRule sbpatz eq .deduction rewrite eq =
  [] ⊢ Type ∋ pick [] (`` # 1) (<>) >>
  (([] -, cent syn <> refl (<> , var (# 0) <>)) ⊢ Type ∋
       pick [] (`` # 0) (<> , var (# 0) <>)
    >> return refl <>)

sigRule piRule : Rule SYNTAX ExJF chk
piRule = binRule [ PI / pat <> oi , pat <> oi ] refl
sigRule = binRule [ SIG / pat <> oi , pat <> oi ] refl

lamRule : Rule SYNTAX ExJF chk
Rule.inpats lamRule = <> , [ PI / pat <> oi , pat <> oi ] -- Π (x : A). B(x)
Rule.sbpats lamRule = <> , [ LA / pat <> oi ]             -- λx. t(x)
Rule.deduction lamRule = prem
  ([] -, cent syn <> refl (<> , var (# 1) <>)) -- , (x : A) ⊢
  chk                                                      -- ∈
  (<> , var (# 1) (<> , var (# 0) <>))            -- B(x)
  (pick [] (d's dzz) (<> , var (# 0) <>))                -- t(x)
  <>
  (return refl <>)


-- impossible to match B(x) as an output of (x : A) ⊢ t ∈ B(x).
-- lamRule' : Rule SYNTAX ExJF chk
-- Rule.inpats lamRule' = <> , [ PI / pat <> oi , pat <> oi ] -- Π (x : A). B(x)
-- Rule.sbpats lamRule' = <> , [ LA / pat <> oi ]             -- λx. t(x)
-- Rule.deduction lamRule' = prem
--   ([] -, cent syn <> (d's dzz) (<> , var (o' (os oz)) <>)) -- , (x : A) ⊢
--   syn                                                      -- ∈
--   <>            -- B(x)
--   {!!} -- (pick [] {!!} (<> , var (os oe) <>))                -- t(x)
--   (<> , {!!})
--   (return refl <>)

appRule : Rule SYNTAX ExJF syn
Rule.inpats appRule = <>
Rule.sbpats appRule = <> , [ AP / pat <> oi , pat <> oi ]
Rule.deduction appRule =
  prem [] syn <> (pick [] (`` # 1) <>) (<> , [ PI / pat <> oi , pat <> oi ])
 (prem [] chk (<> , var (# 1) <>) (pick [] (`` # 0) <>) <>
 (return refl (<> , var (# 1) (<> , [ AN / var (# 0) <> , var (# 2) <> ]))))


pairRule : Rule SYNTAX ExJF chk
pairRule .inpats = <> , [ SIG / pat <> oi , pat <> oi ]
pairRule .sbpats = <> , [ PR / pat <> oi , pat <> oi ]
pairRule .deduction =
  [] ⊢ var (# 1) <> ∋ pick [] (`` # 1) (<>) >>
  ([] ⊢ var (# 1) (<> , [ AN / var (# 0) <> , var (# 2) <> ]) ∋ pick [] (`` # 0) <> >>
    return refl <>)

fstRule : Rule SYNTAX ExJF syn
Rule.inpats fstRule = <>
Rule.sbpats fstRule = <> , [ FST / pat <> oi ]
Rule.deduction fstRule
  = prem [] syn <> (pick [] (d's dzz) <>) (<> , [ SIG / (pat <> oi) , (pat <> oi) ])
         (return refl (<> , (var (o' (os oe)) <>)))


sndRule : Rule SYNTAX ExJF syn
Rule.inpats sndRule = <>
Rule.sbpats sndRule = <> , [ SND / pat <> oi ]
Rule.deduction sndRule
  = prem [] syn <> (pick [] (d's dzz) <>) (<> , [ SIG / (pat <> oi) , (pat <> oi) ])
         (return refl (<> , (var (os oe) (<> , [ FST / var (o' (o' (os oe))) <> ]))))



anRule : Rule SYNTAX ExJF syn
anRule .inpats = <>
anRule .sbpats = <> , [ AN / pat <> oi , pat <> oi ]
anRule .deduction =
  [] ⊢ Type ∋ pick [] (`` # 0) <> >>
  ([] ⊢ var (# 0) <> ∋ pick [] (`` # 0) <> >>
    return refl (<> , var (# 1) <>))

emRule : Rule SYNTAX ExJF chk
emRule .inpats = <> , pat <> oi
emRule .sbpats = <> , [ EM / pat <> oi ]
emRule .deduction =
  [] ⊢ pick [] (`` # 0) <> ∈ pat <> oi >>
  (prem [] chk-eq (((<> , Type) , var (# 0) <>) , var (# 2) <>) [] <>
  (return refl <>))

unRule : Rule SYNTAX ExJF chk
unRule .inpats = <> , Type
unRule .sbpats = <> , [ UN / <> ]
unRule .deduction = return refl <>

vdRule : Rule SYNTAX ExJF chk
vdRule .inpats = <> , [ UN / <> ]
vdRule .sbpats = <> , [ VD / <> ]
vdRule .deduction = return refl <>

paxRule : Rule SYNTAX ExJF syn
paxRule .inpats = <>
paxRule .sbpats = <> , Pax (pat <> oi) (pat <> oi) -- < i.T(i) ] t
paxRule .deduction
  =
  -- (i : PT) ⊢ * ∋ T(i)
  (([] -, cent poi <> refl <>)) ⊢ Type ∋ (pick [] (ds' (d's dzz)) (<> , (var v0 <>))) >>
  -- ⊢ T(0) ∋ t
  ([] ⊢ var v0 (<> , `0) ∋ (pick [] (d's dzz) <>) >>
    (return refl (<> , var (o' v0) (<> , `1))))


patRule : Rule SYNTAX ExJF chk
patRule .inpats = <> , Type
patRule .sbpats = <> , [ PAT / pat <> oi
                             , pat <> oi
                             , pat <> oi ]
patRule .deduction =
  ([] -, cent poi <> refl <>) ⊢ Type ∋ pick [] (`` # 2) (<> , var v0 <>) >>
  ([] ⊢ var (# 0) (<> , `0) ∋ (pick [] (`` # 1) <>) >>
  ([] ⊢ var (# 1) (<> , `1) ∋ (pick [] (`` # 0) <>) >>
  return refl <>))

pavRule : Rule SYNTAX ExJF chk
pavRule .inpats = <> , [ PAT / pat <> oi
                             , pat <> oi
                             , pat <> oi ]
pavRule .sbpats = <> , [ PAV / pat <> oi ]
pavRule .deduction =
  (([] -, cent poi <> refl <>)) ⊢ var (# 3) (<> , var (# 0) <>) ∋ pick [] (`` (# 0)) (<> , var (# 0) <>) >>
  prem [] chk-eq (((<> , (var (# 3) (<> , [ P0 / <> ]))) , (var (# 0) (<> , [ P0 / <> ]))) , var (# 2) <>) [] <>
  (prem [] chk-eq ((((<> , (var (# 3) (<> , [ P1 / <> ]))) , (var (# 0) (<> , [ P1 / <> ]))) , var (# 1) <>)) [] <>
  (return refl <>))

papRule : Rule SYNTAX ExJF syn
papRule .inpats = <>
papRule .sbpats = <> , [ PAP / pat <> oi , pat <> oi ]
papRule .deduction =
  [] ⊢ pick [] (`` # 1) <> ∈ [ PAT / pat <> oi , pat <> oi , pat <> oi ] >>
  prem [] poi <> (pick [] (`` # 0) <>) <>
  (return refl (<> , var (# 3) (<> , var (# 0) <>)))

p0Rule : Rule SYNTAX ExJF poi
p0Rule .inpats = <>
p0Rule .sbpats = <> , `0
p0Rule .deduction = return refl <>

p1Rule : Rule SYNTAX ExJF poi
p1Rule .inpats = <>
p1Rule .sbpats = <> , `1
p1Rule .deduction = return refl <>

muxRule : Rule SYNTAX ExJF poi
muxRule .inpats = <>
muxRule .sbpats = <> , [ MUX / (pat _ oi) , (pat _ oi) , (pat _ oi) ]
muxRule .deduction =
  prem [] poi <> (pick [] (d's (ds' (ds' dzz))) <>) <>
  (prem [] poi <> (pick [] (d's (ds' dzz)) <>) <>
  (prem [] poi <> (pick [] (d's dzz) <>) <>
  (return refl <>)))
