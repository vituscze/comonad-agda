------------------------------------------------------------------------
-- Definition of category operations and their laws.
------------------------------------------------------------------------

module Category where

open import Lib.Relation.Binary.PropositionalEquality
  using (_≡_)

-- Category laws.
record IsCategory
       (_⇒_ : Set → Set → Set)
       (_∘_ : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C))
       (id  : ∀ {A}     → (A ⇒ A)) : Set₁ where
  field
    idʳ : ∀ {A B} (f : A ⇒ B) →
      f ∘ id ≡ f
    idˡ : ∀ {A B} (f : A ⇒ B) →
      id ∘ f ≡ f
    assoc : ∀ {A B C D} (f : C ⇒ D) (g : B ⇒ C) (h : A ⇒ B) →
      f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h

-- Category operations.
record Category
       (_⇒_ : Set → Set → Set) : Set₁ where
  infixr 9 _∘_

  field
    _∘_        : ∀ {A B C} → (B ⇒ C) → (A ⇒ B) → (A ⇒ C)
    id         : ∀ {A}     → (A ⇒ A)
    isCategory : IsCategory _⇒_ _∘_ id
