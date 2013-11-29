module Lib.Algebra.Structures where

open import Lib.Data.Product
open import Lib.Level
open import Lib.Relation.Binary

import Lib.Algebra.FunctionProperties as FunctionProperties

open FunctionProperties using (Op₂)

record IsSemigroup {a ℓ} {A : Set a}
  (≈ : Rel A ℓ) (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    isEquivalence : IsEquivalence ≈
    assoc         : Associative ∙
    ∙-cong        : ∙ Preserves₂ ≈ ⟶ ≈ ⟶ ≈

  open IsEquivalence isEquivalence public

record IsMonoid {a ℓ} {A : Set a}
  (≈ : Rel A ℓ) (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    isSemigroup : IsSemigroup ≈ ∙
    identity    : Identity ε ∙

  open IsSemigroup isSemigroup public

record IsCommutativeMonoid {a ℓ} {A : Set a}
  (≈ : Rel A ℓ) (_∙_ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    isSemigroup : IsSemigroup ≈ _∙_
    identityˡ   : LeftIdentity ε _∙_
    comm        : Commutative _∙_

  open IsSemigroup isSemigroup

record IsCommutativeSemiring {a ℓ} {A : Set a}
  (≈ : Rel A ℓ) (_+_ _*_ : Op₂ A) (0# 1# : A) : Set (a ⊔ ℓ) where
  open FunctionProperties ≈
  field
    +-isCommutativeMonoid : IsCommutativeMonoid ≈ _+_ 0#
    *-isCommutativeMonoid : IsCommutativeMonoid ≈ _*_ 1#
    distribʳ              : _*_ DistributesOverʳ _+_
    zeroˡ                 : LeftZero 0# _*_
