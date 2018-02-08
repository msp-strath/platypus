module Syntax where

open import OPE
open import Datoid

Cx : Set -> Set
data Kind (I : Set) : Set where
  _=>_ : Cx I -> I -> Kind I
Cx I = Bwd (Kind I)

data Desc (I : Set) : Set1 where
  rec' : (K : Kind I) -> Desc I
  _%'_ : (C : Datoid) -> (D : Data C -> Desc I) -> Desc I
  _*'_ : (D E : Desc I) -> Desc I
  One' : Desc I

spD : {I : Set} -> Cx I -> Desc I
spD []         = One'
spD (kz -, k)  = spD kz *' rec' k

Rele : {I : Set} -> (Kind I -> Cx I -> Set) -> Desc I -> Cx I -> Set
Rele R (rec' K) = R K
Rele R (C %' D) = Tag C \ c -> Rele R (D c)
Rele R (D *' E) = Rele R D ** Rele R E
Rele R One'     = Done

DeBr : {I : Set} -> (Kind I -> Cx I -> Set) -> Desc I -> Cx I -> Set
DeBr R (rec' K) kz = R K kz
DeBr R (C %' D) kz = Tag C (\ c -> DeBr R (D c)) kz
DeBr R (D *' E) kz = DeBr R D kz * DeBr R E kz
DeBr R One'     kz = One

data Lang : Set where pat exp : Lang

PatLang : Lang -> Set
PatLang pat = One
PatLang exp = Zero

TmK : {I : Set}(F : I -> Desc I)(l : Lang)(k : Kind I)
      (kz : Cx I) -> Set
data Tm {I : Set}(F : I -> Desc I)(l : Lang)(i : I)
     (kz : Cx I) : Set where
  [_] : Rele (TmK F l) (F i) kz -> Tm F l i kz
  var : {jz : Cx I} -> (Only (jz => i) ** Rele (TmK F l) (spD jz)) kz -> Tm F l i kz
  pat : PatLang l -> Tm F l i kz

DBK : {I : Set}(F : I -> Desc I)(l : Lang)(k : Kind I)
      (kz : Cx I) -> Set
data DB {I : Set}(F : I -> Desc I)(l : Lang)(i : I)
     (kz : Cx I) : Set where
  [_] : DeBr (DBK F l) (F i) kz -> DB F l i kz
  var : {jz : Cx I} -> The (jz => i) kz -> DeBr (DBK F l) (spD jz) kz -> DB F l i kz
  pat : {iz : Cx I} -> PatLang l -> iz <= kz -> DB F l i kz
DBK F l (jz => i) kz = DB F l i (kz ++ jz)

[_]^ : {I : Set}{F : I -> Desc I}{l : Lang}{i : I}{kz : Cx I} ->
       Rele (TmK F l) (F i) ^^ kz -> Tm F l i ^^ kz
[ ts ^ th ]^ = [ ts ] ^ th

TmK F l (jz => i) = jz !- Tm F l i

spine : {I : Set}{F : I -> Desc I}{l : Lang}{jz : Cx I}
        {kz : Cx I} ->
        All (\ k -> TmK F l k ^^ kz) jz ->
        Rele (TmK F l) (spD jz) ^^ kz
spine [] = done^
spine (tz -, t) = spine tz ,^ t

enips : {I : Set}{F : I -> Desc I}{l : Lang}{jz : Cx I}
        {kz : Cx I} ->
        Rele (TmK F l) (spD jz) ^^ kz ->
        All (\ k -> TmK F l k ^^ kz) jz
enips {jz = []} (done ^ th) = []
enips {jz = jz -, x} ((es <[ ec ]> e) ^ th) = (enips (es ^ (lope ec <&= th))) -, (e ^ (rope ec <&= th))

pats : {I : Set}{F : I -> Desc I}{i : I}{kz : Cx I} -> Tm F pat i kz -> Cx I
patsD : {I : Set}{F : I -> Desc I}(D : Desc I){kz : Cx I} -> Rele (TmK F pat) D kz -> Cx I
pats {F = F}{i = i} [ ps ] = patsD (F i) ps
pats (var {jz} (_ <[ _ ]> ps)) = patsD (spD jz) ps
pats {i = i}{kz = kz} (pat <>) = [] -, (kz => i)
patsD (rec' (jz => i)) (th \\ p) = pats p
patsD (C %' D) (c / ps) = patsD (D c) ps
patsD (D *' E) (ps <[ _ ]> qs) = patsD D ps ++ patsD E qs
patsD One' done = []

patsDB : {I : Set}{F : I -> Desc I}{i : I}{kz : Cx I} -> DB F pat i kz -> Cx I
patsDBD : {I : Set}{F : I -> Desc I}(D : Desc I){kz : Cx I} -> DeBr (DBK F pat) D kz -> Cx I
patsDB {F = F}{i = i} [ ps ] = patsDBD (F i) ps
patsDB (var {jz} _ ps) = patsDBD (spD jz) ps
patsDB {i = i}{kz = kz} (pat {iz} <> _) = [] -, (iz => i)
patsDBD (rec' (jz => i)) p = patsDB p
patsDBD (C %' D) (c / ps) = patsDBD (D c) ps
patsDBD (D *' E) (ps , qs) = patsDBD D ps ++ patsDBD E qs
patsDBD One' <> = []

var^ : {I : Set}{F : I -> Desc I}{l : Lang}{jz : Cx I}
       {kz : Cx I}{i : I} ->
       ([] -, (kz => i)) <= jz ->
       Rele (TmK F l) (spD kz) ^^ jz ->
       Tm F l i ^^ jz
var^ x tz with (only ^ x) ,^ tz
var^ x tz | xtz ^ th = var xtz ^ th

match : {I : Set}{F : I -> Desc I}{i : I}{iz kz : Cx I}
        (p : Tm F pat i kz)(e : Tm F exp i ^^ (iz ++ kz)) ->
        Maybe (All (\ k -> TmK F exp k ^^ iz) (pats p))
matchD : {I : Set}{F : I -> Desc I}(D : Desc I){iz kz : Cx I}
         (ps : Rele (TmK F pat) D kz)(es : Rele (TmK F exp) D ^^ (iz ++ kz)) ->
         Maybe (All (\ k -> TmK F exp k ^^ iz) (patsD D ps))
match {F = F}{i = i} [ ps ] ([ es ] ^ th) = matchD (F i) ps (es ^ th)
match {iz = iz}{kz = kz} (var (only <[ pc ]> ps)) (var (only <[ ec ]> es) ^ th) with (oe {_}{iz} <++= lope pc) | (lope ec <&= th)
... | ph' | th' with decide (OPE _) (_ , ph') (_ , th')
match {iz = iz} {kz} (var {jz} (only <[ pc ]> ps)) (var (only <[ ec ]> es) ^ th) | ph' | .ph' | yes refl with thinSplit iz kz th
match {iz = iz} {kz} (var {jz} (only <[ pc ]> ps)) (var (only <[ ec ]> es) ^ .(th0 <++= th1)) | ph' | .ph' | yes refl | mkThinSplit th0 th1 with refines (rope pc) th1
match {iz = iz} {kz} (var {jz} (only <[ pc ]> ps)) (var (only <[ ec ]> es) ^ .(th0 <++= (th1 <&= rope pc))) | ph' | .ph' | yes refl | mkThinSplit th0 .(th1 <&= rope pc) | yes (mkRefines th1) = matchD (spD jz) ps (es ^ (rope ec <&= (th0 <++= th1)))
match {iz = iz} {kz} (var {jz} (only <[ pc ]> ps)) (var (only <[ ec ]> es) ^ .(th0 <++= th1)) | ph' | .ph' | yes refl | mkThinSplit th0 th1 | no = no
match {iz = iz} {kz} (var (only <[ pc ]> ps)) (var (only <[ ec ]> es) ^ th) | ph' | th' | no x = no 
match {iz = iz}{kz = kz}(pat <>) (e ^ th) with thinSplit iz kz th
match {iz = iz} {kz} (pat <>) (e ^ .(th <++= ph)) | mkThinSplit th ph =
  yes ([] -, ((ph \\ e) ^ th))
match _ _ = no
matchD (rec' (jz => i)) {iz} {kz} (ph \\ p) ((th' \\ e) ^ th) with refines ph th'
matchD (rec' (jz => i)) {iz} {kz} (ph \\ p) ((.(th' <&= ph) \\ e) ^ th) | yes (mkRefines th') = match p (e ^ thin++Lemma th th')
matchD (rec' (jz => i)) {iz} {kz} (ph \\ p) ((th' \\ e) ^ th) | no = no
matchD (C %' D) (c / ps) ((c' / es) ^ th) with decide C c c'
matchD (C %' D) (c / ps) ((.c / es) ^ th) | yes refl = matchD (D c) ps (es ^ th)
matchD (C %' D) (c / ps) ((c' / es) ^ th) | no x = no
matchD (D *' E) {iz}{kz} (psl <[ pc ]> psr) ((esl <[ ec ]> esr) ^ th) with thinSplit iz kz th
matchD (D *' E) {iz} {kz} (psl <[ pc ]> psr) ((esl <[ ec ]> esr) ^ .(th0 <++= th1)) | mkThinSplit {iz'}{kz'} th0 th1 with copSplit iz' kz' ec
matchD (D *' E) {iz} {kz} (psl <[ pc ]> psr) ((esl <[ .(ec0 +cop ec1) ]> esr) ^ .(th0 <++= th1)) | mkThinSplit {iz'} {kz'} th0 th1 | mkCopSplit ec0 ec1 with (lope ec1 <&= th1) | (rope ec1 <&= th1)
... | thl | thr with refines (lope pc) thl | refines (rope pc) thr
matchD (D *' E) {iz} {kz} (psl <[ pc ]> psr) ((esl <[ .(ec0 +cop ec1) ]> esr) ^ .(th0 <++= th1)) | mkThinSplit th0 th1 | mkCopSplit ec0 ec1 | .(thl <&= lope pc) | .(thr <&= rope pc) | yes (mkRefines thl) | yes (mkRefines thr) =
  matchD D psl (esl ^ (((lope ec0 <&= th0) <++= thl))) >>= \ sl ->
  matchD E psr (esr ^ (((rope ec0 <&= th0) <++= thr))) >>= \ sr ->
  yes (sl +A+ sr)
matchD (D *' E) {iz} {kz} (psl <[ pc ]> psr) ((esl <[ .(ec0 +cop ec1) ]> esr) ^ .(th0 <++= th1)) | mkThinSplit th0 th1 | mkCopSplit ec0 ec1 | thl | thr | _ | _ = no
matchD One' done (done ^ th) = yes []

record Morph {I : Set}(F : I -> Desc I)(iz jz : Cx I) : Set where
  constructor mkMorph
  field
    {left}      : Cx I
    {replaced}  : Cx I
    renamer : left <= jz
    dealer  : Deal left replaced iz
    substitution : All (\ j -> TmK F exp j ^^ jz) replaced
open Morph public

imor : {I : Set}{F : I -> Desc I}{iz : Cx I} -> Morph F iz iz
imor {iz = iz} = mkMorph oi (dealL iz) []

wmor : {I : Set}{F : I -> Desc I}{iz jz : Cx I} ->
       Morph F iz jz -> (kz : Cx I) -> Morph F (iz ++ kz) (jz ++ kz)
wmor (mkMorph th d ez) kz = mkMorph
  (th <++= oi {iz = kz})
  (dealMoreL d kz)
  (all (_^$ (oi <++= oe {iz = kz})) ez)

wmorImor : {I : Set}{F : I -> Desc I}{iz : Cx I}(kz : Cx I) ->
  wmor (imor {F = F}{iz = iz}) kz == imor
wmorImor {iz = iz} kz rewrite oi<++=oi {iz = iz} kz | dealLMoreL {iz = iz} kz = refl

subst : {I : Set}{F : I -> Desc I}{hz iz iz' jz : Cx I}{i : I} ->
        Tm F exp i iz -> iz <= iz' ->
        (m : Morph F iz' jz)(q : hz == replaced m) ->
        Tm F exp i ^^ jz
substK : {I : Set}{F : I -> Desc I}{hz iz iz' jz : Cx I}(k : Kind I) ->
        TmK F exp k iz -> iz <= iz' ->
        (m : Morph F iz' jz)(q : hz == replaced m) ->
        TmK F exp k ^^ jz
substD : {I : Set}{F : I -> Desc I}{hz iz iz' jz : Cx I}(D : Desc I) ->
         Rele (TmK F exp) D iz -> iz <= iz' ->
         (m : Morph F iz' jz)(q : hz == replaced m) ->
         Rele (TmK F exp) D ^^ jz
hered : {I : Set} {i : I} {hz iz jz kz : Cx I} {F : I -> Desc I} ->
        ([] -, (kz => i)) <= iz ->
        (m : Morph F iz jz)(q : hz == replaced m) ->
        Rele (TmK F exp) (spD kz) ^^ jz -> Tm F exp i ^^ jz
subst {F = F}{i = i}[ es ] th ga q = [_] $^ substD (F i) es th ga q
subst (var {jz} (only <[ xc ]> es)) th ga q =
  hered (lope xc <&= th) ga q (substD (spD jz) es (rope xc <&= th) ga q)
subst (pat ()) _ _ _
substD (rec' k) e th ga q = substK k e th ga q
substD (C %' D) (c / es) th ga q = (c /_) $^ substD (D c) es th ga q
substD (D *' E) (esl <[ c ]> esr) th ga q =
  substD D esl (lope c <&= th) ga q ,^ substD E esr (rope c <&= th) ga q
substD One' _ th ga q = done^
hered (os x) (mkMorph th (ds' d) tz) refl de = var^ (os oe <&= th) de
hered {kz = kz}(os x) (mkMorph th (d's d) (tz -, ((ph \\ t) ^ th'))) refl de =
  subst t (th' <++= ph) (mkMorph oi (dealLR _ kz) (enips de)) refl
hered (o' x) (mkMorph th (d's d) (tz -, _)) refl de =
  hered x (mkMorph th d tz) refl de
hered (o' x) (mkMorph th (ds' d) tz) refl de =
  hered x (mkMorph (o' oi <&= th) d tz) refl de
substK (jz => i) (ph \\ e) th m q = jz !-^ subst e (th <++= ph) (wmor m jz) q

sub : {I : Set}{F : I -> Desc I}{iz jz : Cx I} ->
      Morph F iz jz ->
      {i : I} -> Tm F exp i ^^ iz -> Tm F exp i ^^ jz
sub m (e ^ th) = subst e th m refl

subD : {I : Set}{F : I -> Desc I}{iz jz : Cx I} ->
      Morph F iz jz ->
      (D : Desc I) -> Rele (TmK F exp) D ^^ iz -> Rele (TmK F exp) D  ^^ jz
subD m D (es ^ th) = substD D es th m refl
      
subK : {I : Set}{F : I -> Desc I}{iz jz : Cx I} ->
       Morph F iz jz ->
       {k : Kind I} -> TmK F exp k ^^ iz -> TmK F exp k ^^ jz
subK m {k} (e ^ th) = substK k e th m refl

hered' : {I : Set} {i : I} {hz iz jz kz : Cx I} {F : I -> Desc I} ->
         ([] -, (kz => i)) <= iz ->
         (m : Morph F iz jz)(q : hz == replaced m) ->
         Rele (TmK F exp) (spD kz) ^^ jz -> Tm F exp i ^^ jz
hered' x (mkMorph th d ez) q es with refineDeal d x
hered' x (mkMorph th d ez) q es | .([] -, (_ => _)) , .[] , thl , thr , ds' dzz = var^ (thl <&= th) es
hered' x (mkMorph th d ez) q es | .[] , .([] -, (_ => _)) , thl , thr , d's dzz with thr <?= ez
hered' {kz = kz} x (mkMorph th d ez) refl es | .[] , .([] -, (_ => _)) , thl , thr , d's dzz | [] -, ((ph \\ e) ^ th') =
  sub (mkMorph oi (dealLR _ kz) (enips es)) (e ^ (th' <++= ph))

heredQ : {I : Set} {i : I} {hz iz jz kz : Cx I} {F : I -> Desc I} ->
         (x : ([] -, (kz => i)) <= iz) ->
         (m : Morph F iz jz)(q : hz == replaced m) ->
         (es : Rele (TmK F exp) (spD kz) ^^ jz) ->
         hered x m q es == hered' x m q es
heredQ (os x) (mkMorph th (ds' d) ez) refl es with refineDeal d x
heredQ (os x) (mkMorph th (ds' d) ez) refl es | .[] , .[] , thl , thr , dzz with oe1 thl
heredQ (os x) (mkMorph th (ds' d) ez) refl es | .[] , .[] , .oe , thr , dzz | refl = refl
heredQ (os x) (mkMorph th (d's d) (ez -, e)) refl es with refineDeal d x
heredQ (os x) (mkMorph th (d's d) (ez -, e)) refl es | .[] , .[] , thl , thr , dzz with thr <?= ez
heredQ (os x) (mkMorph th (d's d) (ez -, e)) refl es | .[] , .[] , thl , thr , dzz | [] = refl
heredQ (o' x) (mkMorph th (ds' d) ez) refl es with hered x (mkMorph (o' oi <&= th) d ez) refl es | heredQ x (mkMorph (o' oi <&= th) d ez) refl es
... | z | q with refineDeal d x
heredQ (o' x) (mkMorph th (ds' d) ez) refl es | ._ | refl | .([] -, (_ => _)) , .[] , thl , thr , ds' dzz
  rewrite <&=<&= thl (o' oi) th | <&=oi thl = refl
heredQ (o' x) (mkMorph th (ds' d) ez) refl es | ._ | refl | .[] , .([] -, (_ => _)) , thl , thr , d's dzz with thr <?= ez
heredQ (o' x) (mkMorph th (ds' d) ez) refl es | ._ | refl | .[] , .([] -, (_ => _)) , thl , thr , d's dzz | [] -, e = refl
heredQ (o' x) (mkMorph th (d's d) (ez -, _)) refl es with hered x (mkMorph th d ez) refl es | heredQ x (mkMorph th d ez) refl es
... | z | q with refineDeal d x
heredQ (o' x) (mkMorph th (d's d) (ez -, _)) refl es | ._ | refl | .([] -, (_ => _)) , .[] , thl , thr , ds' dzz = refl
heredQ (o' x) (mkMorph th (d's d) (ez -, _)) refl es | ._ | refl | .[] , .([] -, (_ => _)) , thl , thr , d's dzz with thr <?= ez
... | [] -, e = refl

cmor : {I : Set}{F : I -> Desc I}{iz jz kz : Cx I} ->
       Morph F iz jz -> Morph F jz kz ->  Morph F iz kz
cmor (mkMorph th d ez) m@(mkMorph ph e fz) with refineDeal e th
... | izll , izlr , thl , thr , f with rotateDeal f d
... | izr , g , h =
  mkMorph (thl <&= ph) g (riffle (thr <?= fz) h (all (subK m) ez))

{-
subWQ : {I : Set}{F : I -> Desc I}{iz jz : Cx I} ->
        (mij : Morph F iz jz)(hz : Cx I) ->
        {i : I}(e : Tm F exp i ^^ iz) ->
        sub (wmor mij hz) (e ^$ (oi <++= oe {iz = hz})) == (sub mij e ^$ (oi <++= oe {iz = hz}))
subWQ mij hz ([ es ] ^ th) = {!!}
subWQ mij hz (var {jz} (only <[ ec ]> es) ^ th)
  rewrite
    <&=<++= th oz oi (oe {iz = hz}) | <&=oi th | oe1 (oz <&= oe {iz = hz})
  | <&=<++= (lope ec) oz th (oe {iz = hz}) | oe1 (oz <&= oe {iz = hz})
  | heredQ (lope ec <&= (th <++= oe {iz = hz})) (wmor mij hz) refl (substD (spD jz) es (rope ec <&= (th <++= oe {iz = hz})) (wmor mij hz) refl)
  | heredQ 
  = {!!}
subWQ mij hz (pat () ^ th)
-}

{-
wmorcmor : {I : Set}{F : I -> Desc I}{iz jz kz : Cx I} ->
       (mij : Morph F iz jz)(mjk : Morph F jz kz)(hz : Cx I) ->
       cmor (wmor mij hz) (wmor mjk hz) == wmor (cmor mij mjk) hz
wmorcmor (mkMorph th d ez) (mkMorph th' d' ez') hz
  with refineDeal d' th | refineDeal (dealMoreL d' hz) (th <++= oi {iz = hz}) | refineDealMoreL th d' refl hz
wmorcmor (mkMorph th d ez) (mkMorph th' d' ez') hz | izl , izr , thl , thr , d0 | ._ | refl
  with rotateDeal d0 d | rotateDeal (dealMoreL d0 hz) (dealMoreL d hz) | rotateDealMoreL d0 d refl hz
wmorcmor mij@(mkMorph th d ez) mjk@(mkMorph th' d' ez') hz | izl , izr , thl , thr , d0 | ._ | refl | izm , d1 , d2 | ._ | refl
  rewrite <&=<++= thl (oi {iz = hz}) th' (oi {iz = hz}) | oi<&= (oi {iz = hz})
        | <?=all thr (_^$ (oi <++= oe {iz = hz})) ez'
        | allRiffle (_^$ (oi <++= oe {iz = hz})) (thr <?= ez') d2 (all (subK mjk) ez)
        | allall (_^$ (oi <++= oe {iz = hz})) (subK mjk) _ (\ _ -> refl) ez
        | allall (subK (wmor mjk hz)) (_^$ (oi <++= oe {iz = hz})) _ {!!} ez
        = refl
-}

{-
substCQ : {I : Set}{F : I -> Desc I}{hz iz jz kz : Cx I} ->
          (mij : Morph F iz jz)(mjk : Morph F jz kz) -> hz == replaced mij ->
          {iz0 : Cx I}{i : I}(e : Tm F exp i iz0)(th : iz0 <= iz) ->
          sub mjk (sub mij (e ^ th)) == sub (cmor mij mjk) (e ^ th)
substDCQ : {I : Set}{F : I -> Desc I}{hz iz jz kz : Cx I} ->
           (mij : Morph F iz jz)(mjk : Morph F jz kz) -> hz == replaced mij ->
           {iz0 : Cx I}(D : Desc I)(es : Rele (TmK F exp) D iz0)(th : iz0 <= iz) ->
           subD mjk D (subD mij D (es ^ th)) == subD (cmor mij mjk) D (es ^ th)
heredCQ : {I : Set} {i : I} {hz gz iz jz kz : Cx I} {F : I -> Desc I} ->
          (x : ([] -, (gz => i)) <= iz) ->
          (mij : Morph F iz jz)(mjk : Morph F jz kz) -> hz == replaced mij ->
          (es : Rele (TmK F exp) (spD gz) ^^ jz) ->
          sub mjk (hered x mij refl es) ==
          hered x (cmor mij mjk) refl (subD mjk (spD gz) es)
substCQ {F = F} mij mjk q {i = i} [ es ] th rewrite substDCQ mij mjk q (F i) es th = refl
substCQ mij mjk refl (var {gz} (only <[ ec ]> es)) th
  rewrite heredCQ (lope ec <&= th) mij mjk refl (substD (spD gz) es (rope ec <&= th) mij refl)
        | substDCQ mij mjk refl (spD gz) es (rope ec <&= th)
  = refl
substCQ mij mjk q (pat ()) th
substDCQ mij mjk q D es th = {!!}
heredCQ (os x) (mkMorph th (ds' d) ez) mkj q es = {!!}
heredCQ {gz = gz} (os x) (mkMorph th (d's d) (ez -, ((ph \\ e) ^ ps))) mjk@(mkMorph th' d' ez') q es
  = {!!}
heredCQ (o' x) (mkMorph th (ds' d) ez) mkj refl es = {!!}
-- rewrite heredCQ x (mkMorph (o' oi <&= th) d ez) mkj refl es = {!!}
heredCQ (o' x) (mkMorph th (d's d) ez) mkj q es = {!!}
-}
