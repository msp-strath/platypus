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
pattern Pat T t u = [ PAT  / T , (t , u) ]
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
  sort : Sort → JTag
  _-eq : Sort → JTag


pattern chk-eq = chk -eq
pattern syn-eq = syn -eq
pattern poi-eq = poi -eq

ExJF : JTag -> JForm Sort
ExJF (sort chk) = ([] -, ([] => chk)) <? ([] -, ([] => chk)) ?> []
ExJF (sort syn) = []                  <? ([] -, ([] => syn)) ?> (([] -, ([] => chk)))
ExJF (sort poi) = []                  <? ([] -, ([] => poi)) ?> []
ExJF chk-eq .JForm.inputs = [] -, ([] => chk) -, ([] => chk) -, ([] => chk)
ExJF chk-eq .JForm.subjects = []
ExJF chk-eq .JForm.outputs = []
ExJF syn-eq .JForm.inputs = [] -, ([] => syn) -, ([] => syn)
ExJF syn-eq .JForm.subjects = []
ExJF syn-eq .JForm.outputs = [] -, ([] => chk)
ExJF poi-eq .JForm.inputs = [] -, ([] => poi) -, ([] => poi)
ExJF poi-eq .JForm.subjects = []
ExJF poi-eq .JForm.outputs = []


module _ (let I = Sort) {mz sz : Cx I}{X : Cx I -> Set} where
  private
    F = SYNTAX
    JF = ExJF

  _⊢_∋_>>_ : {iz : Cx I} -> CExt F JF mz iz ->
           (let j = sort chk) ->
           (let open JForm (JF j)) ->
               DB F exp chk (mz ++ iz) ->
               {mz' sz' : Cx I} ->
               Subjects F JF (mz ++ iz) sz mz' sz' subjects ->
               Prems F JF ((mz ++ mz')) sz' X ->
               Prems F JF mz sz X
  G ⊢ T ∋ t >> k = prem G (sort chk) (<> , T) t <> k

  _⊢_∋_≡_>>_ : {iz : Cx I} -> CExt F JF mz iz ->
           (let j = chk-eq) ->
           (let open JForm (JF j)) ->
               DB F exp chk (mz ++ iz) ->
               DB F exp chk (mz ++ iz) ->
               DB F exp chk (mz ++ iz) ->
               Prems F JF mz sz X ->
               Prems F JF mz sz X
  G ⊢ T ∋ t ≡ u >> k = prem G chk-eq (((<> , T) , t) , u) [] <> k


  _⊢_∈_>>_ : {iz : Cx I} -> CExt F JF mz iz ->
           (let j = sort syn) ->
           (let open JForm (JF j)) ->
               -- DB F exp chk (mz ++ iz) ->
               {mz' sz' : Cx I} ->
               Subjects F JF (mz ++ iz) sz mz' sz' subjects ->
               (pz : DB F pat chk iz) ->

               Prems F JF ((mz ++ mz') ++ patsDBD (spD outputs) (<> , pz)) sz' X ->
               Prems F JF mz sz X
  G ⊢ t ∈ T >> k = prem G (sort syn) <> t (<> , T) k

  _⊢_≡_∈_>>_ : {iz : Cx I} -> CExt F JF mz iz ->
           (let j = syn-eq) ->
           (let open JForm (JF j)) ->
               DB F exp syn (mz ++ iz) ->
               DB F exp syn (mz ++ iz) ->
               (pz : DB F pat chk iz) ->
               Prems F JF (mz ++ patsDBD (spD outputs) (<> , pz)) sz X ->
               Prems F JF mz sz X
  G ⊢ t ≡ u ∈ S >> k = prem G syn-eq ((<> , t) , u) [] (<> , S) k

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

typeRule : Rule SYNTAX ExJF (sort chk)
typeRule .inpats = <> , Type
typeRule .sbpats = <> , Type
typeRule .deduction = return refl <>

binRule : (sbpatz : DB SYNTAX pat chk [])
        → patsDB sbpatz
          == (([] -, ([] => chk)) -, (([] -, ([] => syn)) => chk))
        -> Rule SYNTAX ExJF (sort chk)
binRule sbpatz eq .inpats = <> , Type
binRule sbpatz eq .sbpats = <> , sbpatz
binRule sbpatz eq .deduction rewrite eq =
  [] ⊢ Type ∋ pick [] (`` # 1) (<>) >>
  (([] -, cent (sort syn) <> refl (<> , var (# 0) <>)) ⊢ Type ∋
       pick [] (`` # 0) (<> , var (# 0) <>)
    >> return refl <>)

sigRule piRule : Rule SYNTAX ExJF (sort chk)
piRule = binRule [ PI / pat <> oi , pat <> oi ] refl
sigRule = binRule [ SIG / pat <> oi , pat <> oi ] refl

lamRule : Rule SYNTAX ExJF (sort chk)
Rule.inpats lamRule = <> , [ PI / pat <> oi , pat <> oi ] -- Π (x : A). B(x)
Rule.sbpats lamRule = <> , [ LA / pat <> oi ]             -- λx. t(x)
Rule.deduction lamRule = prem
  ([] -, cent (sort syn) <> refl (<> , var (# 1) <>)) -- , (x : A) ⊢
  (sort chk)                                                      -- ∈
  (<> , var (# 1) (<> , var (# 0) <>))            -- B(x)
  (pick [] (`` # 0) (<> , var (# 0) <>))                -- t(x)
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

appRule : Rule SYNTAX ExJF (sort syn)
Rule.inpats appRule = <>
Rule.sbpats appRule = <> , [ AP / pat <> oi , pat <> oi ]
Rule.deduction appRule =
  prem [] (sort syn) <> (pick [] (`` # 1) <>) (<> , [ PI / pat <> oi , pat <> oi ])
 (prem [] (sort chk) (<> , var (# 1) <>) (pick [] (`` # 0) <>) <>
 (return refl (<> , var (# 1) (<> , [ AN / var (# 0) <> , var (# 2) <> ]))))


pairRule : Rule SYNTAX ExJF (sort chk)
pairRule .inpats = <> , [ SIG / pat <> oi , pat <> oi ]
pairRule .sbpats = <> , [ PR / pat <> oi , pat <> oi ]
pairRule .deduction =
  [] ⊢ var (# 1) <> ∋ pick [] (`` # 1) (<>) >>
  ([] ⊢ var (# 1) (<> , [ AN / var (# 0) <> , var (# 2) <> ]) ∋ pick [] (`` # 0) <> >>
    return refl <>)

fstRule : Rule SYNTAX ExJF (sort syn)
Rule.inpats fstRule = <>
Rule.sbpats fstRule = <> , [ FST / pat <> oi ]
Rule.deduction fstRule
  = prem [] (sort syn) <> (pick [] (`` # 0) <>) (<> , [ SIG / (pat <> oi) , (pat <> oi) ])
         (return refl (<> , (var (# 1) <>)))


sndRule : Rule SYNTAX ExJF (sort syn)
Rule.inpats sndRule = <>
Rule.sbpats sndRule = <> , [ SND / pat <> oi ]
Rule.deduction sndRule
  = prem [] (sort syn) <> (pick [] (`` # 0) <>) (<> , [ SIG / (pat <> oi) , (pat <> oi) ])
         (return refl (<> , (var (# 0) (<> , [ FST / var (# 2) <> ]))))



anRule : Rule SYNTAX ExJF (sort syn)
anRule .inpats = <>
anRule .sbpats = <> , [ AN / pat <> oi , pat <> oi ]
anRule .deduction =
  [] ⊢ Type ∋ pick [] (`` # 0) <> >>
  ([] ⊢ var (# 0) <> ∋ pick [] (`` # 0) <> >>
    return refl (<> , var (# 1) <>))

emRule : Rule SYNTAX ExJF (sort chk)
emRule .inpats = <> , pat <> oi
emRule .sbpats = <> , [ EM / pat <> oi ]
emRule .deduction =
  [] ⊢ pick [] (`` # 0) <> ∈ pat <> oi >>
  (prem [] chk-eq (((<> , Type) , var (# 0) <>) , var (# 2) <>) [] <>
  (return refl <>))

unRule : Rule SYNTAX ExJF (sort chk)
unRule .inpats = <> , Type
unRule .sbpats = <> , [ UN / <> ]
unRule .deduction = return refl <>

vdRule : Rule SYNTAX ExJF (sort chk)
vdRule .inpats = <> , [ UN / <> ]
vdRule .sbpats = <> , [ VD / <> ]
vdRule .deduction = return refl <>

paxRule : Rule SYNTAX ExJF (sort syn)
paxRule .inpats = <>
paxRule .sbpats = <> , Pax (pat <> oi) (pat <> oi) -- < i.T(i) ] t
paxRule .deduction
  =
  -- (i : PT) ⊢ * ∋ T(i)
  (([] -, cent (sort poi) <> refl <>)) ⊢ Type ∋ (pick [] (`` # 1) (<> , (var (# 0) <>))) >>
  -- ⊢ T(0) ∋ t
  ([] ⊢ var (# 0) (<> , `0) ∋ (pick [] (`` # 0) <>) >>
    (return refl (<> , var (# 1) (<> , `1))))


patRule : Rule SYNTAX ExJF (sort chk)
patRule .inpats = <> , Type
patRule .sbpats = <> , [ PAT / pat <> oi
                             , pat <> oi
                             , pat <> oi ]
patRule .deduction =
  ([] -, cent (sort poi) <> refl <>) ⊢ Type ∋ pick [] (`` # 2) (<> , var (# 0) <>) >>
  ([] ⊢ var (# 0) (<> , `0) ∋ (pick [] (`` # 1) <>) >>
  ([] ⊢ var (# 1) (<> , `1) ∋ (pick [] (`` # 0) <>) >>
  return refl <>))

pavRule : Rule SYNTAX ExJF (sort chk)
pavRule .inpats = <> , [ PAT / pat <> oi
                             , pat <> oi
                             , pat <> oi ]
pavRule .sbpats = <> , [ PAV / pat <> oi ]
pavRule .deduction =
  (([] -, cent (sort poi) <> refl <>)) ⊢ var (# 3) (<> , var (# 0) <>) ∋ pick [] (`` (# 0)) (<> , var (# 0) <>) >>
  prem [] chk-eq (((<> , (var (# 3) (<> , [ P0 / <> ]))) , (var (# 0) (<> , [ P0 / <> ]))) , var (# 2) <>) [] <>
  (prem [] chk-eq ((((<> , (var (# 3) (<> , [ P1 / <> ]))) , (var (# 0) (<> , [ P1 / <> ]))) , var (# 1) <>)) [] <>
  (return refl <>))

papRule : Rule SYNTAX ExJF (sort syn)
papRule .inpats = <>
papRule .sbpats = <> , [ PAP / pat <> oi , pat <> oi ]
papRule .deduction =
  [] ⊢ pick [] (`` # 1) <> ∈ [ PAT / pat <> oi , pat <> oi , pat <> oi ] >>
  prem [] (sort poi) <> (pick [] (`` # 0) <>) <>
  (return refl (<> , var (# 3) (<> , var (# 0) <>)))

p0Rule : Rule SYNTAX ExJF (sort poi)
p0Rule .inpats = <>
p0Rule .sbpats = <> , `0
p0Rule .deduction = return refl <>

p1Rule : Rule SYNTAX ExJF (sort poi)
p1Rule .inpats = <>
p1Rule .sbpats = <> , `1
p1Rule .deduction = return refl <>

muxRule : Rule SYNTAX ExJF (sort poi)
muxRule .inpats = <>
muxRule .sbpats = <> , [ MUX / (pat _ oi) , (pat _ oi) , (pat _ oi) ]
muxRule .deduction =
  prem [] (sort poi) <> (pick [] (`` # 2) <>) <>
  (prem [] (sort poi) <> (pick [] (`` # 1) <>) <>
  (prem [] (sort poi) <> (pick [] (`` # 0) <>) <>
  (return refl <>)))


typeEq : Rule SYNTAX ExJF chk-eq
typeEq .inpats = ((<> , Type) , Type) , Type
typeEq .sbpats = <>
typeEq .deduction = return refl <>

emEq : Rule SYNTAX ExJF chk-eq
emEq .inpats = ((<> , [ EM / pat _ oi ]) , [ EM / pat _ oi ]) , [ EM / pat _ oi ]
emEq .sbpats = <>
emEq .deduction =
  [] ⊢ var (# 1) <> ≡ var (# 0) <> ∈ pat _ oi >> (return refl <>)

binEq : (sbpatz : DB SYNTAX pat chk [])
        → patsDB sbpatz
          == (([] -, ([] => chk)) -, (([] -, ([] => syn)) => chk)) → Rule SYNTAX ExJF chk-eq
binEq T eq .inpats = ((<> , Type) , T ) , T
binEq T eq .sbpats = <>
binEq T eq .deduction rewrite eq =
   [] ⊢ Type ∋ var (# 3) <> ≡ var (# 1) <> >>
  (([] -, cent (sort syn) <> refl (<> , var (# 3) <>)) ⊢ Type ∋ var (# 3) (<> , var (# 0) <>) ≡ var (# 1) (<> , var (# 0) <>)
  >> return refl <>)

piEta : Rule SYNTAX ExJF chk-eq
piEta .inpats = ((<> , [ PI / (pat _ oi , pat _ oi) ]) , (pat _ oi)) , (pat _ oi)
piEta .sbpats = <>
piEta .deduction =
  ([] -, cent (sort syn) <> refl (<> , var (# 3) <>)) ⊢ var (# 3) (<> , var (# 0) <>) ∋ f (# 2) ≡ f (# 1)
    >> return refl <>
 where
   G = (([] -, ([] => chk) -, (([] -, ([] => syn)) => chk) -, ([] => chk) -, ([] => chk) -, ([] => syn)))
   f : The ([] => chk) G → DB SYNTAX exp chk G
   f n = [ EM / [ AP / [ AN / (var n <>) , [ PI / var (# 4) <> , var (# 3) <> ] ] , [ EM / var (# 0) <> ] ] ]

sigEta : Rule SYNTAX ExJF chk-eq
sigEta .inpats = ((<> , [ SIG / (pat _ oi , pat _ oi) ]) , (pat _ oi)) , (pat _ oi)
sigEta .sbpats = <>
sigEta .deduction =
  [] ⊢ var (# 3) <> ∋ [ EM / `fst (# 1) ]
                    ≡ [ EM / `fst (# 0) ] >>
   ([] ⊢ var (# 2) (<> , `fst (# 1))
                    ∋ [ EM / `snd (# 1) ]
                    ≡ [ EM / `snd (# 0) ] >>
    return refl <>)
  where
    G = ([] -, ([] => chk) -, (([] -, ([] => syn)) => chk) -, ([] => chk) -, ([] => chk))
    `fst : The ([] => chk) G → DB SYNTAX exp syn G
    `fst v = [ FST / [ AN / (var v <>) , [ SIG / (var (# 3) <>) , var (# 2) <> ] ] ]
    `snd : The ([] => chk) G → DB SYNTAX exp syn G
    `snd v = [ SND / [ AN / (var v <>) , [ SIG / (var (# 3) <>) , var (# 2) <> ] ] ]

unEta : Rule SYNTAX ExJF chk-eq
unEta .inpats = ((<> , [ UN / <> ]) , pat _ oi) , pat _ oi
unEta .sbpats = <>
unEta .deduction = return refl <>


patEta : Rule SYNTAX ExJF chk-eq
patEta .inpats = ((<> , Pat (pat _ oi) (pat _ oi) (pat _ oi)) , (pat _ oi)) , (pat _ oi)
patEta .sbpats = <>
patEta .deduction =
  ([] -, cent (sort poi) <> refl <>) ⊢ var (# 5) (<> , (var (# 0) <>)) ∋ f (# 2) ≡ f (# 1)
  >> return refl <>
 where
   G = ([] -, (([] -, ([] => poi)) => chk) -, ([] => chk) -, ([] => chk) -, ([] => chk) -, ([] => chk) -, ([] => poi))
   f : The ([] => chk) G → DB SYNTAX exp chk G
   f v = [ EM / [ PAP / [ AN / (var v <>) , Pat (var (# 5) <>) (var (# 4) <>) (var (# 3) <>) ] , (var (# 0) <>) ] ]

-- Var rule?
-- -| x : S
-- ------------
-- x = x ∈ S
-- Cannot have non-linear patterns, and we have to say how to
-- propagate the S from the context.
-- Possibly some extra options in Prem?
-- varEq : Rule SYNTAX ExJF syn-eq
-- varEq .inpats = (<> , (pat _ oi)) , pat _ oi
-- varEq .sbpats = <>
-- varEq .deduction = {!!}


anEq1 : Rule SYNTAX ExJF syn-eq
anEq1 .inpats = (<> , [ AN / [ EM / pat _ oi ] , pat _ oi ]) , (pat _ oi)
anEq1 .sbpats = <>
anEq1 .deduction =
  [] ⊢ var (# 2) <> ≡ var (# 0) <> ∈ pat _ oi >>
  return refl (<> , var (# 0) <>)


anEq2 : Rule SYNTAX ExJF syn-eq
anEq2 .inpats = (<> , pat _ oi) , [ AN / [ EM / pat _ oi ] , pat _ oi ]
anEq2 .sbpats = <>
anEq2 .deduction =
  [] ⊢ var (# 2) <> ≡ var (# 1) <> ∈ pat _ oi >>
  return refl (<> , var (# 0) <>)

apEq : Rule SYNTAX ExJF syn-eq
apEq .inpats = (<> , [ AP / pat _ oi , pat _ oi ]) , [ AP / pat _ oi , pat _ oi ]
apEq .sbpats = <>
apEq .deduction =
  [] ⊢ var (# 3) <> ≡ var (# 1) <> ∈ [ PI / pat _ oi , pat _ oi ] >>
  (  [] ⊢ var (# 1) <> ∋ var (# 4) <> ≡ var (# 2) <> >>
  return refl (<> , var (# 0) (<> , [ AN / var (# 4) <> , var (# 1) <> ])) )


fstEq : Rule SYNTAX ExJF syn-eq
fstEq .inpats = (<> , [ FST / pat <> oi ]) , [ FST / pat <> oi ]
fstEq .sbpats = <>
fstEq .deduction
  = [] ⊢ var (# 1) <> ≡ var (# 0) <> ∈ [ SIG / pat _ oi , pat _ oi ] >>
    (return refl (<> , var (# 1) <>))

sndEq : Rule SYNTAX ExJF syn-eq
sndEq .inpats = (<> , [ SND / pat <> oi ]) , [ SND / pat <> oi ]
sndEq .sbpats = <>
sndEq .deduction
  = [] ⊢ var (# 1) <> ≡ var (# 0) <> ∈ [ SIG / pat _ oi , pat _ oi ] >>
    (return refl (<> , var (# 0) (<> , [ FST / var (# 3) <> ])))

papEq : Rule SYNTAX ExJF syn-eq
papEq .inpats = (<> , [ PAP / pat _ oi , pat _ oi ]) , [ PAP / pat _ oi , pat _ oi ]
papEq .sbpats = <>
papEq .deduction =
  [] ⊢ var (# 3) <> ≡ var (# 1) <> ∈ Pat (pat _ oi) (pat _ oi) (pat _ oi) >>
  prem [] poi-eq ((<> , (var (# 5) <>)) , (var (# 3) <>)) [] <>
  (return refl (<> , var (# 2) (<> , var (# 5) <>)))
