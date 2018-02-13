module Sum where

open import OPE
open import Syntax
open import Datoid

disjoint : ∀ {I} {iz jz : Bwd I} → Cop iz jz (iz ++ jz)
disjoint {iz = []} {[]} = czz
disjoint {iz = iz -, x} {[]} = cs' disjoint
disjoint {jz = jz -, x} = c's disjoint


oinl : ∀ {I} {iz jz : Bwd I} → iz <= (iz ++ jz)
oinl = lope disjoint

oinr : ∀ {I} {iz jz : Bwd I} → jz <= (iz ++ jz)
oinr = rope disjoint

wdeal : ∀ {I} {iz jz : Bwd (Kind I)} {w w₁ : Bwd (Kind I)} →
       Deal w w₁ jz → Deal (iz ++ w) w₁ (iz ++ jz)
wdeal {iz = iz} dzz = dealL (iz ++ [])
wdeal {iz = iz} (ds' d) = ds' (wdeal d)
wdeal {iz = iz} (d's d) = d's (wdeal d)


module _ {I : Set} (F : I → Desc I) where
  idSpineK  : {x : Kind I} → TmK F exp x ([] -, x)

  idSpine : ∀ {iz : Cx I} → Rele (TmK F exp) (spD iz) iz
  idSpine {[]} = done
  idSpine {iz -, x} = idSpine {iz} <[ disjoint {iz = iz} ]> (idSpineK {x})
  idSpineK {x => x₁} = oi \\ (var (only <[ (disjoint {iz = ([] -, (x => x₁))}) ]> idSpine {x}))

  omor : ∀ {iz jz} → iz <= jz → Morph F iz jz
  left (omor th) = _
  replaced (omor th) = []
  renamer (omor th) = th
  dealer (omor th) = dealL _
  substitution (omor th) = []

  lwmor : ∀ {iz jz kz} → Morph F jz kz → Morph F (iz ++ jz) (iz ++ kz)
  left (lwmor {iz} r) = iz ++ r .left
  replaced (lwmor r) = r .replaced
  renamer (lwmor r) = oi <++= r .renamer
  dealer (lwmor r) = wdeal (r .dealer)
  substitution (lwmor r) = all (subK (omor oinr)) (r .substitution)

  casemor : ∀ {iz jz kz} → Morph F iz kz → Morph F jz kz → Morph F (iz ++ jz) kz
  left (casemor l r) = l .left
  replaced (casemor {iz} {jz} l r) = l .replaced ++ jz
  renamer (casemor l r) = l .renamer
  dealer (casemor l r) = dealMoreR (l .dealer) _
  substitution (casemor {iz} {jz} l r) = l .substitution +A+ enips (subD r (spD jz) (idSpine {jz} ^ oi))
