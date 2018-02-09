module Judge where

open import Datoid
open import OPE
open import Syntax

data Mode : Set where input subject output : Mode

record JForm (I : Set) : Set where
  constructor _<?_?>_
  field
    inputs subjects outputs : Cx I

record CEnt {I J : Set}(F : I -> Desc I)(JF : J -> JForm I)(k : Kind I)(iz : Cx I) : Set where
  constructor cent
  field
    varJ : J
  open JForm (JF varJ)
  field
    varIp : DeBr (DBK F pat) (spD inputs) []
    varSb : Deal [] ([] -, k) subjects
    varOp : DeBr (DBK F exp) (spD outputs) (iz ++ patsDBD (spD inputs) varIp)

data CExt {I J : Set}(F : I -> Desc I)(JF : J -> JForm I)(mz : Cx I) : (iz : Cx I) -> Set where
  [] : CExt F JF mz []
  _-,_ : {iz : Cx I}{k : Kind I} -> CExt F JF mz iz -> CEnt F JF k (mz ++ iz) -> CExt F JF mz (iz -, k)

data Subjects {I J : Set}(F : I -> Desc I)(JF : J -> JForm I)(mz sz : Cx I) : Cx I -> Cx I -> Cx I -> Set where
  [] : Subjects F JF mz sz [] sz []
  pick : forall {kz jz' jz i sz1 sz2 mz1} ->
         Subjects F JF mz sz mz1 sz1 kz ->
         Deal sz2 ([] -, (jz' => i)) sz1 ->
         DeBr (DBK F exp) (spD jz') (mz ++ jz) ->
         Subjects F JF mz sz (mz1 -, (jz' => i)) sz2 (kz -, (jz => i))


data Prems {I J : Set}(F : I -> Desc I)(JF : J -> JForm I)(mz sz : Cx I)(X : Cx I -> Set) : Set where
  return : [] == sz -> X mz -> Prems F JF mz sz X
  fail   : Prems F JF mz sz X
  prem   : {iz : Cx I} -> CExt F JF mz iz ->
           (j : J) ->
           let open JForm (JF j)
           in  DeBr (DBK F exp) (spD inputs) (mz ++ iz) ->
               {mz' sz' : Cx I} -> Subjects F JF (mz ++ iz) sz mz' sz' subjects ->
               (pz : DeBr (DBK F pat) (spD outputs) []) ->
               Prems F JF ((mz ++ mz') ++ patsDBD (spD outputs) pz) sz' X ->
               Prems F JF mz sz X

record Rule {I J : Set}(F : I -> Desc I)(JF : J -> JForm I)(j : J) : Set where
  open JForm (JF j)
  field
    inpats  : DeBr (DBK F pat) (spD inputs) []
    sbpats  : DeBr (DBK F pat) (spD subjects) []
  incx = patsDBD (spD inputs) inpats
  sbcx = patsDBD (spD subjects) sbpats
  field
    deduction : Prems F JF incx sbcx (DeBr (DBK F exp) (spD outputs))

open Rule public
