module Syntax where

open import OPE
open import Datoid

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public

Cx : Set -> Set
data Kind (I : Set) : Set where
  _=>_ : Cx I -> I -> Kind I
Cx I = Bwd (Kind I)

data Desc (I : Set) : Set1 where
  rec' : (K : Kind I) -> Desc I
  _%'_ : (C : Datoid) -> (D : Data C -> Desc I) -> Desc I
  _*'_ : (D E : Desc I) -> Desc I
  One' : Desc I

Rele : {I : Set} -> (Kind I -> Cx I -> Set) -> Desc I -> Cx I -> Set
Rele R (rec' K) = R K
Rele R (C %' D) = Tag C \ c -> Rele R (D c)
Rele R (D *' E) = Rele R D ** Rele R E
Rele R One'     = Done

TmK : {I : Set}(F : I -> Desc I)(V : Kind I -> Cx I -> Set)(k : Kind I)
      (kz : Cx I) -> Set
Sp : {I : Set}(F : I -> Desc I)(V : Kind I -> Cx I -> Set)(jz : Cx I)
     (kz : Cx I) -> Set
data Tm {I : Set}(F : I -> Desc I)(V : Kind I -> Cx I -> Set)(i : I)
     (kz : Cx I) : Set where
  [_] : Rele (TmK F V) (F i) kz -> Tm F V i kz
  var : {jz : Cx I} -> (V (jz => i) ** Sp F V jz) kz -> Tm F V i kz

TmK F V (jz => i) = jz !- Tm F V i

Sp F V []        = Done
Sp F V (jz -, j) = Sp F V jz ** TmK F V j

spine : {I : Set}{F : I -> Desc I}{V : Kind I -> Cx I -> Set}{jz : Cx I}
        {kz : Cx I} ->
        All (\ k -> TmK F V k ^^ jz) kz ->
        Sp F V kz ^^ jz
spine [] = done^
spine (tz -, t) = spine tz ,^ t

var^ : {I : Set}{F : I -> Desc I}{jz : Cx I}
       {kz : Cx I}{i : I} ->
       ([] -, (kz => i)) <= jz ->
       All (\ k -> TmK F Only k ^^ jz) kz ->
       Tm F Only i ^^ jz
var^ x tz with (only ^ x) ,^ spine tz
var^ x tz | xtz ^ th = var xtz ^ th

data Stub {I : Set} : Kind I -> Cx I -> Set where
  stub : {i : I}{iz : Cx I} -> Stub ([] => i) iz
  
PatVars : {I : Set}{F : I -> Desc I}
          (iz : Cx I)(j : I) ->
          Tm F Stub j iz -> Cx I
PatVarsD : {I : Set}{F : I -> Desc I}
           (iz : Cx I)(D : Desc I) ->
           Rele (TmK F Stub) D iz -> Cx I
PatVars {F = F} iz j [ ps ] = PatVarsD iz (F j) ps
PatVars iz j (var (stub <[ c ]> done)) = [] -, (iz => j)
PatVarsD iz (rec' (jz => i)) (th \\ p) = PatVars _ i p
PatVarsD iz (C %' D) (c / ps) =
  PatVarsD iz (D c) ps
PatVarsD iz (D *' E) (ps <[ co ]> qs) =
  PatVarsD _ D ps ++
  PatVarsD _ E qs
PatVarsD iz One' _ = []

match : {I : Set}{F : I -> Desc I}(iz jz : Cx I){i : I} ->
        (p : Tm F Stub i iz) -> Tm F Only i ^^ (jz ++ iz) ->
        Maybe (All (\ k -> TmK F Only k ^^ jz) (PatVars iz i p))
matchD : {I : Set}{F : I -> Desc I}(iz jz : Cx I)(D : Desc I) ->
         (ps : Rele (TmK F Stub) D iz) ->
         Rele (TmK F Only) D ^^ (jz ++ iz) ->
         Maybe (All (\ k -> TmK F Only k ^^ jz) (PatVarsD iz D ps))
match {F = F} iz jz {i = i} [ ps ] ([ ts ] ^ th) =
  matchD iz jz (F i) ps (ts ^ th)
match iz jz [ ps ] (var _ ^ th) = no
match iz jz (var (stub <[ c ]> done)) (t ^ th) with thinSplit jz iz th
match iz jz (var (stub <[ c ]> done)) (t ^ ._) | mkThinSplit th0 th1 =
  yes ([] -, ((th1 \\ t) ^ th0))
matchD iz jz (rec' (iz' => i)) (ph' \\ p) ((th' \\ t) ^ th)
  = refines ph' th' >>= \ { (mkRefines ph) ->
      match _ jz p (t ^ thin++Lemma th ph) }
matchD iz jz (C %' D) (pt / ps) ((tt / ts) ^ th) with decide C pt tt
matchD iz jz (C %' D) (pt / ps) ((.pt / ts) ^ th) | yes refl =
  matchD iz jz (D pt) ps (ts ^ th)
matchD iz jz (C %' D) (pt / ps) ((tt / ts) ^ th) | no x = no
matchD iz jz (D *' E) (pl <[ pc ]> pr) ((tl <[ tc ]> tr) ^ th)
  with thinSplit jz iz th
matchD iz jz (D *' E) (pl <[ pc ]> pr) ((tl <[ tc ]> tr) ^ .(th <++= ph))
  | mkThinSplit {lz0}{lz1} th ph with copSplit lz0 lz1 tc
matchD iz jz (D *' E) (pl <[ pc ]> pr) ((tl <[ .(c0 +cop c1) ]> tr) ^ .(th <++= ph)) | mkThinSplit {lz0} {lz1} th ph | mkCopSplit c0 c1 with lope pc | lope c1 <&= ph | refines (lope pc) (lope c1 <&= ph) | rope pc | rope c1 <&= ph | refines (rope pc) (rope c1 <&= ph)
matchD iz jz (D *' E) (pl <[ pc ]> pr) ((tl <[ .(c0 +cop c1) ]> tr) ^ .(th <++= ph)) | mkThinSplit {lz0} {lz1} th ph | mkCopSplit {jz0}{iz0}{jz1}{iz1} c0 c1 | al | .(ph0 <&= al) | yes (mkRefines ph0) | ar | .(ph1 <&= ar) | yes (mkRefines ph1) =
  matchD _ jz0 D pl (tl ^ (oi <++= ph0)) >>= \ ga0 ->
  matchD _ jz1 E pr (tr ^ (oi <++= ph1)) >>= \ ga1 ->
  yes (all (_^$ (lope c0 <&= th)) ga0 +A+ all (_^$ (rope c0 <&= th)) ga1) 
matchD iz jz (D *' E) (pl <[ pc ]> pr) ((tl <[ .(c0 +cop c1) ]> tr) ^ .(th <++= ph)) | mkThinSplit {lz0} {lz1} th ph | mkCopSplit c0 c1 | al | bl | _ | ar | br | _ = no
matchD iz jz One' ps (ts ^ th) = yes []


record Morph {I : Set}(F : I -> Desc I)(hz iz jz : Cx I) : Set where
  constructor mkMorph
  field
    {thinned} : Cx I
    renamer : thinned <= jz
    dealer  : Deal thinned hz iz
    substitution : All (\ j -> TmK F Only j ^^ jz) hz

subst : {I : Set}{F : I -> Desc I}{hz iz iz' jz : Cx I}{i : I} ->
        Tm F Only i iz -> iz <= iz' ->
        Morph F hz iz' jz ->
        Tm F Only i ^^ jz
substD : {I : Set}{F : I -> Desc I}{hz iz iz' jz : Cx I}(D : Desc I) ->
         Rele (TmK F Only) D iz -> iz <= iz' ->
         Morph F hz iz' jz ->
         Rele (TmK F Only) D ^^ jz
substK : {I : Set}{F : I -> Desc I}{hz iz iz' jz : Cx I}(k : Kind I) ->
         TmK F Only k iz -> iz <= iz' ->
         Morph F hz iz' jz ->
         TmK F Only k ^^ jz
substs : {I : Set}{F : I -> Desc I}{hz iz iz' jz : Cx I}(kz : Cx I) ->
         Sp F Only kz iz -> iz <= iz' ->
         Morph F hz iz' jz ->
         All (\ k -> TmK F Only k ^^ jz) kz
hered : {I : Set} {i : I} {hz iz jz kz : Cx I} {F : I -> Desc I} ->
        ([] -, (kz => i)) <= iz ->
        Morph F hz iz jz ->
        All (\ k -> TmK F Only k ^^ jz) kz -> Tm F Only i ^^ jz
subst {F = F}{i = i}[ ts ] th ga = [_] $^ substD (F i) ts th ga
subst (var (only <[ xc ]> ts)) th ga with substs _ ts (rope xc <&= th) ga
... | de = hered (lope xc <&= th) ga de
substD (rec' k) t th ga = substK k t th ga
substD (C %' D) (c / ts) th ga = (c /_) $^ substD (D c) ts th ga
substD (D *' E) (tsl <[ c ]> tsr) th ga =
  substD D tsl (lope c <&= th) ga ,^ substD E tsr (rope c <&= th) ga
substD One' ts th ga = done^
substs [] done th ga = []
substs (kz -, k) (ts <[ c ]> t) th ga =
  substs kz ts (lope c <&= th) ga -, substK k t (rope c <&= th) ga
substK (kz => i) (ph' \\ t) ph (mkMorph th d tz)
  with subst t (ph <++= ph')
       (mkMorph (th <++= oi {iz = kz}) (dealMoreL d kz)
         (all (_^$ (oi <++= oe {iz = kz})) tz))
... | t' ^ th' with thinSplit _ kz th'
substK (kz => i) (ph' \\ t) ph (mkMorph th d tz)
    | t' ^ ._ | mkThinSplit th0' th1' =
    (th1' \\ t') ^ th0'
hered (os i) (mkMorph th (ds' d) tz) de = var^ (os oe <&= th) de
hered (os i) (mkMorph th (d's d) (tz -, ((ph \\ t) ^ th'))) de =
  subst t (th' <++= ph) (mkMorph oi (dealLR _ _) de)
hered (o' i) (mkMorph th (d's d) (tz -, _)) de =
  hered i (mkMorph th d tz) de
hered (o' i) (mkMorph th (ds' d) tz) de =
  hered i (mkMorph (o' oi <&= th) d tz) de
