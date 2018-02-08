module Datoid where

data _==_ {X : Set}(x : X) : X -> Set where
  refl : x == x
{-# BUILTIN EQUALITY _==_ #-}

data Zero : Set where

record One : Set where
  constructor <>

data Decide (X : Set) : Set where
  yes : X -> Decide X
  no  : (X -> Zero) -> Decide X

record Datoid : Set1 where
  field
    Data   : Set
    decide : (x y : Data) -> Decide (x == y)
open Datoid public

ZERO : Datoid
Data ZERO = Zero
decide ZERO () y

ONE : Datoid
Data ONE = One
decide ONE <> <> = yes refl

record Sg (S : Set)(T : S -> Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg public
_*_ : Set -> Set -> Set
S * T = Sg S \ _ -> T
infixr 4 _,_ _*_

SG : (S : Datoid)(T : Data S -> Datoid) -> Datoid
Data (SG S T) = Sg (Data S) \ s -> Data (T s)
decide (SG S T) (s , t) (s' , t') with decide S s s'
decide (SG S T) (s , t) (.s , t') | yes refl with decide (T s) t t'
decide (SG S T) (s , t) (.s , .t) | yes refl | yes refl = yes refl
decide (SG S T) (s , t) (.s , t') | yes refl | no x = no \ { refl -> x refl }
decide (SG S T) (s , t) (s' , t') | no x = no \ { refl -> x refl }
