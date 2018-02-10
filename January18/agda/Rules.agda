{-# OPTIONS --postfix-projections #-}

module Rules where

open import Datoid
open import OPE
open import Tm
open import Syntax
open import Judge

-----------------------------------------------------------
-- Maybe move back into Tm/Syntax
v0 : {I : Set} -> {i : I} -> {iz : Bwd I} → The i (iz -, i)
v0 = os oe

pattern Pax t u = [ PAX  / (t , u) ]
pattern Type    = [ TYPE / <>      ]
pattern `0      = [ P0   / <>      ]
pattern `1      = [ P1   / <>      ]

-------------------------------

ExJF : Sort -> JForm Sort
ExJF chk = ([] -, ([] => chk)) <? ([] -, ([] => chk)) ?> []
ExJF syn = []                  <? ([] -, ([] => syn)) ?> (([] -, ([] => chk)))
ExJF poi = []                  <? ([] -, ([] => poi)) ?> []

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

lamRule : Rule SYNTAX ExJF chk
Rule.inpats lamRule = <> , [ PI / pat <> oi , pat <> oi ] -- Π (x : A). B(x)
Rule.sbpats lamRule = <> , [ LA / pat <> oi ]             -- λx. t(x)
Rule.deduction lamRule = prem
  ([] -, cent syn <> refl (<> , var (o' (os oz)) <>)) -- , (x : A) ⊢
  chk                                                      -- ∈
  (<> , var (o' (os oe)) (<> , var (os oe) <>))            -- B(x)
  (pick [] (d's dzz) (<> , var (os oe) <>))                -- t(x)
  <>
  (return refl <>)

appRule : Rule SYNTAX ExJF syn
Rule.inpats appRule = <>
Rule.sbpats appRule = <> , [ AP / pat <> oi , pat <> oi ]
Rule.deduction appRule =
  prem [] syn <> (pick [] (ds' (d's dzz)) <>)
     (<> , [ PI / pat <> oi , pat <> oi ])
     (prem [] chk (<> , var (o' (os oe)) <>) (pick [] (d's dzz) <>)
       <>
       (return refl (<> , var (o' (os oe)) (<> , [ AN / var (os oe) <> , var (o' (o' (os oe))) <> ]))))


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
  ([] -, cent poi <> refl <>) ⊢ Type ∋ pick [] (ds' (ds' (d's dzz))) (<> , var v0 <>) >>
  ([] ⊢ var v0      (<> , `0) ∋ (pick [] (ds' (d's dzz)) <>) >>
  ([] ⊢ var (o' v0) (<> , `1) ∋ (pick [] (d's dzz)       <>) >>
  return refl <>))
