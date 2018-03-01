module OPE where

open import Datoid

data Bwd (I : Set) : Set where
  [] : Bwd I
  _-,_ : Bwd I -> I -> Bwd I

infixl 5 _-,_

data _<=_ {I : Set} : Bwd I -> Bwd I -> Set where
  oz :                                     []    <=     []
  os : forall {iz jz j} -> iz <= jz -> (iz -, j) <= (jz -, j)
  o' : forall {iz jz j} -> iz <= jz ->  iz       <= (jz -, j)

The : {I : Set} -> I -> Bwd I -> Set
The i iz = ([] -, i) <= iz

oe : {I : Set}{iz : Bwd I} -> [] <= iz
oe {_} {[]}      = oz
oe {_} {iz -, i} = o' oe

oi : {I : Set}{iz : Bwd I} -> iz <= iz
oi {_} {[]}      = oz
oi {_} {iz -, i} = os oi

_<&=_ : {I : Set}{iz jz kz : Bwd I} -> iz <= jz -> jz <= kz -> iz <= kz
th    <&= o' ph = o' (th <&= ph)
oz    <&= oz    = oz
os th <&= os ph = os (th <&= ph)
o' th <&= os ph = o' (th <&= ph)

oi<&= : {I : Set}{iz jz : Bwd I}(th : iz <= jz) -> (oi <&= th) == th
oi<&= oz = refl
oi<&= (os th) rewrite oi<&= th = refl
oi<&= (o' th) rewrite oi<&= th = refl

<&=oi : {I : Set}{iz jz : Bwd I}(th : iz <= jz) -> (th <&= oi) == th
<&=oi oz = refl
<&=oi (os th) rewrite <&=oi th = refl
<&=oi (o' th) rewrite <&=oi th = refl

<&=<&= : {I : Set}{hz iz jz kz : Bwd I}
         (th : hz <= iz)(ph : iz <= jz)(ps : jz <= kz) ->
         (th <&= (ph <&= ps)) == ((th <&= ph) <&= ps)
<&=<&= th ph (o' ps) rewrite <&=<&= th ph ps = refl
<&=<&= th (o' ph) (os ps) rewrite <&=<&= th ph ps = refl
<&=<&= (o' th) (os ph) (os ps) rewrite <&=<&= th ph ps = refl
<&=<&= (os th) (os ph) (os ps) rewrite <&=<&= th ph ps = refl
<&=<&= oz oz oz = refl

oe1 : {I : Set}{iz : Bwd I}(th : [] <= iz) -> th == oe
oe1 oz = refl
oe1 (o' th) rewrite oe1 th = refl

OPE : {I : Set} -> Bwd I -> Datoid
Data (OPE jz) = Sg _ \ iz -> iz <= jz
decide (OPE .[]) (.[] , oz) (.[] , oz) = yes refl
decide (OPE .(_ -, _)) (.(_ -, _) , os th) (.(_ -, _) , os ph) with decide (OPE _) (_ , th) (_ , ph)
decide (OPE .(_ -, _)) (.(_ -, _) , os th) (.(_ -, _) , os .th) | yes refl = yes refl
decide (OPE .(_ -, _)) (.(_ -, _) , os th) (.(_ -, _) , os ph) | no x = no \ { refl -> x refl }
decide (OPE .(_ -, _)) (.(_ -, _) , os th) (kz , o' ph) = no \ ()
decide (OPE .(_ -, _)) (iz , o' th) (.(_ -, _) , os ph) = no \ ()
decide (OPE .(_ -, _)) (iz , o' th) (kz , o' ph) with decide (OPE _) (_ , th) (_ , ph)
decide (OPE .(_ -, _)) (.kz , o' th) (kz , o' .th) | yes refl = yes refl
decide (OPE .(_ -, _)) (iz , o' th) (kz , o' ph) | no x = no \ { refl -> x refl }

data Maybe (X : Set) : Set where
  yes : X -> Maybe X
  no  : Maybe X

_>>=_ : {X Y : Set} -> Maybe X -> (X -> Maybe Y) -> Maybe Y
no >>= _  = no
yes x >>= k = k x

data Refines {I : Set}{iz jz kz : Bwd I}(th : jz <= kz) : iz <= kz -> Set where
  mkRefines : (ph : iz <= jz) -> Refines th (ph <&= th)

refines : {I : Set}{iz jz kz : Bwd I}(th : jz <= kz)(ph : iz <= kz) ->
  Maybe (Refines th ph)
refines oz oz = yes (mkRefines oz)
refines (os th) (os ph) =
  refines th ph >>= \ { (mkRefines ph) -> yes (mkRefines (os ph)) }
refines (os th) (o' ph) =
  refines th ph >>= \ { (mkRefines ph) -> yes (mkRefines (o' ph)) }
refines (o' th) (os ph) = no
refines (o' th) (o' ph) =
  refines th ph >>= \ { (mkRefines ph) -> yes (mkRefines ph) }

record _^^_ {I : Set}(P : Bwd I -> Set)(iz : Bwd I) : Set where
  constructor _^_
  field
    {support} : Bwd I
    thing     : P support
    thinning  : support <= iz

_$^_ : {I : Set}{P Q : Bwd I -> Set} -> ({iz : Bwd I} -> P iz -> Q iz) ->
       {iz : Bwd I} -> P ^^ iz -> Q ^^ iz
f $^ (t ^ th) = f t ^ th

_^$_ : {I : Set}{P : Bwd I -> Set} ->
       {iz jz : Bwd I} -> P ^^ iz -> iz <= jz -> P ^^ jz
(t ^ th) ^$ ph = t ^ (th <&= ph)

data Cop {I : Set} : Bwd I -> Bwd I -> Bwd I -> Set where
  czz : Cop [] [] []
  css : forall {iz jz kz i} -> Cop iz jz kz ->
          Cop (iz -, i) (jz -, i) (kz -, i)
  c's : forall {iz jz kz i} -> Cop iz jz kz ->
          Cop  iz       (jz -, i) (kz -, i)
  cs' : forall {iz jz kz i} -> Cop iz jz kz ->
          Cop (iz -, i)  jz       (kz -, i)

lope : {I : Set}{iz jz kz : Bwd I} -> Cop iz jz kz -> iz <= kz
lope czz = oz
lope (css x) = os (lope x)
lope (c's x) = o' (lope x)
lope (cs' x) = os (lope x)

rope : {I : Set}{iz jz kz : Bwd I} -> Cop iz jz kz -> jz <= kz
rope czz = oz
rope (css x) = os (rope x)
rope (c's x) = os (rope x)
rope (cs' x) = o' (rope x)

data Union {I : Set}{iz jz lz : Bwd I} : (iz <= lz) -> (jz <= lz) -> Set where
  mkUnion : {kz : Bwd I}(c : Cop iz jz kz)(th : kz <= lz) ->
    Union (lope c <&= th) (rope c <&= th)
union : {I : Set}{iz jz lz : Bwd I}(phi : iz <= lz)(phj : jz <= lz) ->
  Union phi phj
union oz oz = mkUnion czz oz
union (os phi) (os phj) with union phi phj
union (os .(lope c <&= th)) (os .(rope c <&= th)) | mkUnion c th =
  mkUnion (css c) (os th)
union (os phi) (o' phj) with union phi phj
union (os .(lope c <&= th)) (o' .(rope c <&= th)) | mkUnion c th =
  mkUnion (cs' c) (os th)
union (o' phi) (os phj) with union phi phj
union (o' .(lope c <&= th)) (os .(rope c <&= th)) | mkUnion c th =
  mkUnion (c's c) (os th)
union (o' phi) (o' phj) with union phi phj
union (o' .(lope c <&= th)) (o' .(rope c <&= th)) | mkUnion c th =
  mkUnion c (o' th)

record _**_ {I : Set}(P Q : Bwd I -> Set)(iz : Bwd I) : Set where
  constructor _<[_]>_
  field
    {lsupp rsupp} : Bwd I
    outl : P lsupp
    pcop : Cop lsupp rsupp iz
    outr : Q rsupp

_,^_ :  {I : Set}{P Q : Bwd I -> Set}{iz : Bwd I} ->
        P ^^ iz -> Q ^^ iz -> (P ** Q) ^^ iz
(p ^ phi) ,^ (q ^ phj) with union phi phj
(p ^ .(lope c <&= th)) ,^ (q ^ .(rope c <&= th)) | mkUnion c th
  = (p <[ c ]> q) ^ th

proj^ :  {I : Set}{P Q : Bwd I -> Set}{iz : Bwd I} ->
        (P ** Q) ^^ iz -> P ^^ iz * Q ^^ iz
proj^ ((outl <[ pcop ]> outr) ^ thinning) = (outl ^ (lope pcop <&= thinning)) , (outr ^ ((rope pcop <&= thinning)))


data Done {I : Set} : Bwd I -> Set where
  done : Done []

done^ : {I : Set}{iz : Bwd I} -> Done ^^ iz
done^ = done ^ oe

_++_ : {I : Set} -> Bwd I -> Bwd I -> Bwd I
xz ++ [] = xz
xz ++ (yz -, y) = (xz ++ yz) -, y

_<++=_ : {I : Set}{iz0 iz1 jz0 jz1 : Bwd I} ->
         iz0 <= jz0 -> iz1 <= jz1 -> (iz0 ++ iz1) <= (jz0 ++ jz1)
th <++= oz = th
th <++= os ph = os (th <++= ph)
th <++= o' ph = o' (th <++= ph)

assoc++ : {I : Set}(iz jz kz : Bwd I) ->
  ((iz ++ jz) ++ kz) == (iz ++ (jz ++ kz))
assoc++ iz jz [] = refl
assoc++ iz jz (kz -, k) rewrite assoc++ iz jz kz = refl

id++ : {I : Set}(iz : Bwd I) → ([] ++ iz) == iz
id++ [] = refl
id++ (iz -, i) rewrite id++ iz = refl

thin++Lemma : {I : Set}{ijz kz iz' jz' kz' : Bwd I} ->
  ijz <= (iz' ++ jz') -> kz <= kz' ->
  (ijz ++ kz) <= (iz' ++ (jz' ++ kz'))
thin++Lemma th oz      = th
thin++Lemma th (os ph) = os (thin++Lemma th ph)
thin++Lemma th (o' ph) = o' (thin++Lemma th ph)

data ThinSplit {I : Set}(jz' kz' : Bwd I) :
    {iz : Bwd I} -> iz <= (jz' ++ kz') -> Set
  where
  mkThinSplit : {jz kz : Bwd I}(th : jz <= jz')(ph : kz <= kz') ->
                ThinSplit jz' kz' (th <++= ph)

thinSplit : {I : Set}(jz' kz' : Bwd I){iz : Bwd I}(th : iz <= (jz' ++ kz'))
            -> ThinSplit jz' kz' th
thinSplit jz' [] th = mkThinSplit th oz
thinSplit jz' (kz' -, k) (os th) with thinSplit jz' kz' th
thinSplit jz' (kz' -, k) (os .(th <++= ph)) | mkThinSplit th ph
  = mkThinSplit th (os ph)
thinSplit jz' (kz' -, k) (o' th) with thinSplit jz' kz' th
thinSplit jz' (kz' -, k) (o' .(th <++= ph)) | mkThinSplit th ph
  = mkThinSplit th (o' ph)

_+cop_ : {I : Set}{iz0 jz0 kz0 iz1 jz1 kz1 : Bwd I} ->
  Cop iz0 jz0 kz0 -> Cop iz1 jz1 kz1 ->
  Cop (iz0 ++ iz1) (jz0 ++ jz1) (kz0 ++ kz1)
c0 +cop czz = c0
c0 +cop css c1 = css (c0 +cop c1)
c0 +cop c's c1 = c's (c0 +cop c1)
c0 +cop cs' c1 = cs' (c0 +cop c1)

data CopSplit {I : Set}(kz0 kz1 : Bwd I) :
  {iz jz : Bwd I} -> Cop iz jz (kz0 ++ kz1) -> Set
  where
  mkCopSplit : {iz0 iz1 jz0 jz1 : Bwd I} ->
    (c0 : Cop iz0 jz0 kz0)(c1 : Cop iz1 jz1 kz1) ->
    CopSplit kz0 kz1 (c0 +cop c1)

copSplit : {I : Set}(kz0 kz1 : Bwd I)
  {iz jz : Bwd I}(c : Cop iz jz (kz0 ++ kz1)) -> CopSplit kz0 kz1 c
copSplit kz0 [] c = mkCopSplit c czz
copSplit kz0 (kz1 -, x) (css c) with copSplit kz0 kz1 c
copSplit kz0 (kz1 -, x) (css .(c0 +cop c1)) | mkCopSplit c0 c1 =
  mkCopSplit c0 (css c1)
copSplit kz0 (kz1 -, x) (c's c) with copSplit kz0 kz1 c
copSplit kz0 (kz1 -, x) (c's .(c0 +cop c1)) | mkCopSplit c0 c1 =
  mkCopSplit c0 (c's c1)
copSplit kz0 (kz1 -, x) (cs' c) with copSplit kz0 kz1 c
copSplit kz0 (kz1 -, x) (cs' .(c0 +cop c1)) | mkCopSplit c0 c1 =
  mkCopSplit c0 (cs' c1)

record _!-_ {I : Set}(jz : Bwd I)(P : Bwd I -> Set)(iz : Bwd I) : Set where
  constructor _\\_
  field
    {relevant} : Bwd I
    bind       : relevant <= jz
    body       : P (iz ++ relevant)

_!-^_ : {I : Set}(jz : Bwd I){P : Bwd I -> Set}{iz : Bwd I} ->
  P ^^ (iz ++ jz) -> (jz !- P) ^^ iz
jz !-^ (p ^ th) with thinSplit _ jz th
jz !-^ (p ^ .(th <++= ph)) | mkThinSplit th ph = (ph \\ p) ^ th

unbind : {I : Set}(jz : Bwd I){P : Bwd I -> Set}{iz : Bwd I}
   -> (jz !- P) ^^ iz -> P ^^ (iz ++ jz)
unbind jz ((bind \\ body) ^ thinning) = body ^ (thinning <++= bind)

data Only {I : Set}(i : I) : Bwd I -> Set where
  only : Only i ([] -, i)

record Tag {I : Set}(C : Datoid)(T : Data C -> Bwd I -> Set)(iz : Bwd I) : Set
  where
  constructor _/_
  field
    tag    : Data C
    stuff  : T tag iz
infixr 4 _/_

_/^_ : {I : Set}{C : Datoid}{T : Data C -> Bwd I -> Set}{iz : Bwd I} ->
  (c : Data C)(t : T c ^^ iz) -> Tag C T ^^ iz
c /^ (t ^ th) = (c / t) ^ th

data All {I : Set}(P : I -> Set) : Bwd I -> Set where
  [] : All P []
  _-,_ : forall {iz i} -> All P iz -> P i -> All P (iz -, i)

all : {I : Set}{P Q : I -> Set} ->
      ({i : I} -> P i -> Q i) ->
      {iz : Bwd I} -> All P iz -> All Q iz
all f [] = []
all f (pz -, p) = all f pz -, f p

allall : {I : Set}{P Q R : I -> Set} ->
      (f : {i : I} -> Q i -> R i)(g : {i : I} -> P i -> Q i)(h : {i : I} -> P i -> R i) ->
      ({i : I}(p : P i) -> f (g p) == h p) ->
      {iz : Bwd I}(pz : All P iz) -> all f (all g pz) == all h pz
allall f g h q [] = refl
allall f g h q (pz -, p) rewrite allall f g h q pz | q p = refl

_+A+_ : {I : Set}{P : I -> Set}{iz jz : Bwd I} ->
  All P iz -> All P jz -> All P (iz ++ jz)
pz +A+ [] = pz
pz +A+ (qz -, q) = (pz +A+ qz) -, q

_<?=_ : {I : Set}{P : I -> Set}{iz jz : Bwd I} ->
        iz <= jz -> All P jz -> All P iz
oz    <?= pz = []
os th <?= (pz -, p) = (th <?= pz) -, p
o' th <?= (pz -, p) =  th <?= pz

oi<?= : {I : Set}{P : I -> Set}{iz : Bwd I} ->
        (pz : All P iz) -> (oi <?= pz) == pz
oi<?= [] = refl
oi<?= (pz -, p) rewrite oi<?= pz = refl

<?=all : {I : Set}{P Q : I -> Set}{iz jz : Bwd I} ->
        (th : iz <= jz)(f : {i : I} -> P i -> Q i)(pz : All P jz) ->
        (th <?= all f pz) == all f (th <?= pz)
<?=all oz f [] = refl
<?=all (os th) f (pz -, p) rewrite <?=all th f pz = refl
<?=all (o' th) f (pz -, p) rewrite <?=all th f pz = refl

oi<++=oi : {I : Set}{iz : Bwd I}(jz : Bwd I) -> (oi {iz = iz} <++= oi {iz = jz}) == oi
oi<++=oi [] = refl
oi<++=oi {iz = iz} (jz -, j) rewrite oi<++=oi {iz = iz} jz = refl

<&=<++= : {I : Set}{iz jz kz iz' jz' kz' : Bwd I}
  (th : iz <= jz)(th' : iz' <= jz')
  (ph : jz <= kz)(ph' : jz' <= kz') ->
  ((th <++= th') <&= (ph <++= ph')) == ((th <&= ph) <++= (th' <&= ph'))
<&=<++= th th' ph (o' ph') rewrite <&=<++= th th' ph ph' = refl
<&=<++= th (o' th') ph (os ph') rewrite <&=<++= th th' ph ph' = refl
<&=<++= th (os th') ph (os ph') rewrite <&=<++= th th' ph ph' = refl
<&=<++= th oz ph oz = refl

data Deal {I : Set} : Bwd I -> Bwd I -> Bwd I -> Set where
  dzz : Deal [] [] []
  ds' : forall {iz jz kz i} -> Deal iz jz kz -> Deal (iz -, i) jz (kz -, i)
  d's : forall {iz jz kz i} -> Deal iz jz kz -> Deal iz (jz -, i) (kz -, i)

dealL : {I : Set}(iz : Bwd I) -> Deal iz [] iz
dealL [] = dzz
dealL (iz -, _) = ds' (dealL iz)

dealMoreL :  {I : Set}{iz jz kz : Bwd I} -> Deal iz jz kz ->
  (lz : Bwd I) -> Deal (iz ++ lz) jz (kz ++ lz)
dealMoreL d [] = d
dealMoreL d (lz -, x) = ds' (dealMoreL d lz)

dealLMoreL : {I : Set}{iz : Bwd I}(kz : Bwd I) ->
  dealMoreL (dealL iz) kz == dealL (iz ++ kz)
dealLMoreL [] = refl
dealLMoreL {iz = iz} (kz -, k) rewrite dealLMoreL {iz = iz} kz = refl

dealMoreR :  {I : Set}{iz jz kz : Bwd I} -> Deal iz jz kz ->
  (lz : Bwd I) -> Deal iz (jz ++ lz) (kz ++ lz)
dealMoreR d [] = d
dealMoreR d (lz -, x) = d's (dealMoreR d lz)

dealLR : {I : Set}(iz jz : Bwd I) -> Deal iz jz (iz ++ jz)
dealLR iz [] = dealL iz
dealLR iz (jz -, j) = d's (dealLR iz jz)

dealLeft : {I : Set}{iz jz kz : Bwd I} → Deal iz jz kz → iz <= kz
dealLeft dzz     = oz
dealLeft (ds' d) = os (dealLeft d)
dealLeft (d's d) = o' (dealLeft d)

dealRight : {I : Set}{iz jz kz : Bwd I} → Deal iz jz kz → jz <= kz
dealRight dzz     = oz
dealRight (ds' d) = o' (dealRight d)
dealRight (d's d) = os (dealRight d)


refineDeal : {I : Set}{iz' jz' kz kz' : Bwd I} ->
             Deal iz' jz' kz' -> kz <= kz' ->
             Sg _ \ iz -> Sg _ \ jz -> iz <= iz' * jz <= jz' * Deal iz jz kz
refineDeal d oz = [] , [] , oe , oe , dzz
refineDeal (ds' d) (o' th) with refineDeal d th
... | iz , jz , phi , phj , e = iz , jz , o' phi , phj , e
refineDeal (d's d) (o' th) with refineDeal d th
... | iz , jz , phi , phj , e = iz , jz , phi , o' phj , e
refineDeal (ds' d) (os th) with refineDeal d th
... | iz , jz , phi , phj , e = (iz -, _) , jz , os phi , phj , ds' e
refineDeal (d's d) (os th) with refineDeal d th
... | iz , jz , phi , phj , e = iz , (jz -, _) , phi , os phj , d's e

refineDealOi : {I : Set}{iz jz kz : Bwd I} ->
               (d : Deal iz jz kz) ->
               refineDeal d oi == (iz , jz , oi , oi , d)
refineDealOi dzz = refl
refineDealOi (ds' d) rewrite refineDealOi d = refl
refineDealOi (d's d) rewrite refineDealOi d = refl

refineDealMoreL : {I : Set}{jzl jzr iz jz : Bwd I}(th : iz <= jz)(d : Deal jzl jzr jz) ->
                  {izl izr : Bwd I}{thl : izl <= jzl}{thr : izr <= jzr}{c : Deal izl izr iz} ->
                  refineDeal d th == (izl , izr , thl , thr , c) ->
                  (hz : Bwd I) ->
                  refineDeal (dealMoreL d hz) (th <++= oi {iz = hz}) ==
                  (izl ++ hz , izr , (thl <++= oi {iz = hz}) , thr , dealMoreL c hz)
refineDealMoreL th d q [] = q
refineDealMoreL th d q (hz -, h) with refineDeal (dealMoreL d hz) (th <++= oi {iz = hz}) | refineDealMoreL th d q hz
refineDealMoreL th d q (hz -, h) | ._ | refl = refl

refineDealMoreL' : {I : Set}{jzl jzr iz jz : Bwd I}(th : iz <= jz)(d : Deal jzl jzr jz) ->
                  {izl izr : Bwd I}{thl : izl <= jzl}{thr : izr <= jzr}{c : Deal izl izr iz} ->
                  refineDeal d th == (izl , izr , thl , thr , c) ->
                  (hz : Bwd I) ->
                  refineDeal (dealMoreL d hz) (th <++= oe {iz = hz}) ==
                  (izl , izr , (thl <++= oe {iz = hz}) , thr , c)
refineDealMoreL' th d q [] = q
refineDealMoreL' th d q (hz -, h) with refineDeal (dealMoreL d hz) (th <++= oe {iz = hz}) | refineDealMoreL' th d q hz
refineDealMoreL' th d q (hz -, h) | ._ | refl = refl

rotateDeal : {I : Set}{izll izlr izl izr iz : Bwd I} ->
             Deal izll izlr izl -> Deal izl izr iz ->
             Sg _ \ jz -> Deal izll jz iz * Deal izlr izr jz
rotateDeal d (d's e) with rotateDeal d e
... | jz , f , g = (jz -, _) , d's f , d's g
rotateDeal (d's d) (ds' e) with rotateDeal d e
... | jz , f , g = (jz -, _) , d's f , ds' g
rotateDeal (ds' d) (ds' e) with rotateDeal d e
... | jz , f , g = jz , ds' f , g
rotateDeal dzz dzz = [] , dzz , dzz

rotateDealL : {I : Set}{izll izlr izl : Bwd I} ->
               (d : Deal izll izlr izl) ->
               rotateDeal d (dealL izl) == (izlr , d , dealL izlr)
rotateDealL dzz = refl
rotateDealL (ds' d) rewrite rotateDealL d = refl
rotateDealL (d's d) rewrite rotateDealL d = refl

rotateDealLR : {I : Set}{izll izlr izl : Bwd I} ->
               (d : Deal izll izlr izl) (izr : Bwd I) ->
  rotateDeal d (dealLR izl izr) == ((izlr ++ izr) , dealMoreR d izr , dealLR izlr izr)
rotateDealLR d [] = rotateDealL d
rotateDealLR d (izr -, i) rewrite rotateDealLR d izr = refl

rotateDealMoreL :  {I : Set}{izll izlr izl izr iz : Bwd I} ->
                   (dl : Deal izll izlr izl)(d : Deal izl izr iz) ->
                   {jz : Bwd I}{d' : Deal izll jz iz}{dr : Deal izlr izr jz} ->
                   rotateDeal dl d == (jz , d' , dr) ->
                   (hz : Bwd I) ->
                   rotateDeal (dealMoreL dl hz) (dealMoreL d hz) ==
                   (jz , dealMoreL d' hz , dr)
rotateDealMoreL dl d q [] = q
rotateDealMoreL dl d q (hz -, h) with rotateDeal (dealMoreL dl hz) (dealMoreL d hz) | rotateDealMoreL dl d q hz
rotateDealMoreL dl d q (hz -, h) | .(_ , dealMoreL _ hz , _) | refl = refl

riffle : {I : Set}{P : I -> Set}{iz jz kz : Bwd I} ->
         All P iz -> Deal iz jz kz -> All P jz ->
         All P kz
riffle pzl dzz pzr = []
riffle (pzl -, p) (ds' d) pzr = riffle pzl d pzr -, p
riffle pzl (d's d) (pzr -, p) = riffle pzl d pzr -, p

allRiffle : {I : Set}{P Q : I -> Set}(f : {i : I} -> P i -> Q i)
            {iz jz kz : Bwd I} ->
            (pzl : All P iz)(d : Deal iz jz kz)(pzr : All P jz) ->
            (all f (riffle pzl d pzr)) == riffle (all f pzl) d (all f pzr)
allRiffle f pzl dzz pzr = refl
allRiffle f (pzl -, p) (ds' d) pzr rewrite allRiffle f pzl d pzr = refl
allRiffle f pzl (d's d) (pzr -, p) rewrite allRiffle f pzl d pzr = refl
