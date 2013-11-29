module Lib.Relation.Binary where

open import Lib.Level

Rel : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
Rel A ℓ = A → A → Set ℓ

Reflexive : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Reflexive _∼_ = ∀ {x} → x ∼ x

Symmetric : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Symmetric _∼_ = ∀ {x y} → x ∼ y → y ∼ x

Transitive : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Transitive _∼_ = ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z

_Preserves₂_⟶_⟶_ : ∀ {a b c ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b} {C : Set c} →
  (A → B → C) → Rel A ℓ₁ → Rel B ℓ₂ → Rel C ℓ₃ → Set _
_∙_ Preserves₂ P ⟶ Q ⟶ R = ∀ {x y u v} → P x y → Q u v → R (x ∙ u) (y ∙ v)

record IsEquivalence {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) : Set (a ⊔ ℓ) where
  field
    refl  : Reflexive  _≈_
    sym   : Symmetric  _≈_
    trans : Transitive _≈_
