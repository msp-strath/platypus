module OPE where

open import Datoid

data Bwd (I : Set) : Set where
  [] : Bwd I
  _-,_ : Bwd I -> I -> Bwd I

data _<=_ {I : Set} : Bwd I -> Bwd I -> Set where
  oz :                                     []    <=     []
  os : forall {iz jz j} -> iz <= jz -> (iz -, j) <= (jz -, j)
  o' : forall {iz jz j} -> iz <= jz ->  iz       <= (jz -, j)

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

data Only {I : Set}(i : I) : Bwd I -> Set where
  only : Only i ([] -, i)

record Tag {I : Set}(C : Datoid)(T : Data C -> Bwd I -> Set)(iz : Bwd I) : Set
  where
  constructor _/_
  field
    tag    : Data C
    stuff  : T tag iz

data All {I : Set}(P : I -> Set) : Bwd I -> Set where
  [] : All P []
  _-,_ : forall {iz i} -> All P iz -> P i -> All P (iz -, i)

all : {I : Set}{P Q : I -> Set} ->
      ({i : I} -> P i -> Q i) ->
      {iz : Bwd I} -> All P iz -> All Q iz
all f [] = []
all f (pz -, p) = all f pz -, f p

_+A+_ : {I : Set}{P : I -> Set}{iz jz : Bwd I} ->
  All P iz -> All P jz -> All P (iz ++ jz)
pz +A+ [] = pz
pz +A+ (qz -, q) = (pz +A+ qz) -, q

data Deal {I : Set} : Bwd I -> Bwd I -> Bwd I -> Set where
  dzz : Deal [] [] []
  ds' : forall {iz jz kz i} -> Deal iz jz kz -> Deal (iz -, i) jz (kz -, i)
  d's : forall {iz jz kz i} -> Deal iz jz kz -> Deal iz (jz -, i) (kz -, i)

dealL : {I : Set}(iz : Bwd I) -> Deal iz [] iz
dealL [] = dzz
dealL (iz -, _) = ds' (dealL iz)

dealLR : {I : Set}(iz jz : Bwd I) -> Deal iz jz (iz ++ jz)
dealLR iz [] = dealL iz
dealLR iz (jz -, _) = d's (dealLR iz jz)

dealMoreL :  {I : Set}{iz jz kz : Bwd I} -> Deal iz jz kz ->
  (lz : Bwd I) -> Deal (iz ++ lz) jz (kz ++ lz)
dealMoreL d [] = d
dealMoreL d (lz -, x) = ds' (dealMoreL d lz)
