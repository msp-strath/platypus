module Datoid where

data _==_ {X : Set}(x : X) : X -> Set where
  refl : x == x
{-# BUILTIN EQUALITY _==_ #-}

data Zero : Set where

data Decide (X : Set) : Set where
  yes : X -> Decide X
  no  : (X -> Zero) -> Decide X

record Datoid : Set1 where
  field
    Data   : Set
    decide : (x y : Data) -> Decide (x == y)
open Datoid public


