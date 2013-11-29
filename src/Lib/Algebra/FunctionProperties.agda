open import Lib.Relation.Binary

module Lib.Algebra.FunctionProperties
  {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

open import Lib.Algebra.FunctionProperties.Core public
open import Lib.Data.Product

Associative : Op₂ A → Set _
Associative _∙_ = ∀ x y z → ((x ∙ y) ∙ z) ≈ (x ∙ (y ∙ z))

Commutative : Op₂ A → Set _
Commutative _∙_ = ∀ x y → (x ∙ y) ≈ (y ∙ x)

LeftIdentity : A → Op₂ A → Set _
LeftIdentity e _∙_ = ∀ x → (e ∙ x) ≈ x

RightIdentity : A → Op₂ A → Set _
RightIdentity e _∙_ = ∀ x → (x ∙ e) ≈ x

Identity : A → Op₂ A → Set _
Identity e ∙ = LeftIdentity e ∙ × RightIdentity e ∙

LeftZero : A → Op₂ A → Set _
LeftZero z _∙_ = ∀ x → (z ∙ x) ≈ z

_DistributesOverʳ_ : Op₂ A → Op₂ A → Set _
_*_ DistributesOverʳ _+_ = ∀ x y z → ((y + z) * x) ≈ ((y * x) + (z * x))
