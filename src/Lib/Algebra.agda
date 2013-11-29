module Lib.Algebra where

open import Lib.Algebra.Structures
open import Lib.Level
open import Lib.Relation.Binary

import Lib.Algebra.FunctionProperties as FunctionProperties

open FunctionProperties using (Op₂)

record CommutativeSemiring c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _*_
  infixl 6 _+_
  infix  4 _≈_
  field
    Carrier               : Set c
    _≈_                   : Rel Carrier ℓ
    _+_                   : Op₂ Carrier
    _*_                   : Op₂ Carrier
    0#                    : Carrier
    1#                    : Carrier
    isCommutativeSemiring : IsCommutativeSemiring _≈_ _+_ _*_ 0# 1#
