module ComonadDef where

open import Function
open import Relation.Binary.PropositionalEquality

-- Comonad definition using extract and extend.
record IsComonad {W : Set → Set}
       (extract : ∀ {A}   →  W A → A)
       (extend  : ∀ {A B} → (W A → B) → W A → W B) : Set₁ where
  field
    extract-idʳ : ∀ {A} (x : W A) →
      extend extract x ≡ x
    extract-idˡ : ∀ {A B} (f : W A → B) (x : W A) →
      extract (extend f x) ≡ f x
    extend-asso : ∀ {A B C} (f : W B → C) (g : W A → B) (x : W A) →
      extend f (extend g x) ≡ extend (f ∘ extend g) x

record Comonad (W : Set → Set) : Set₁ where
  field
    extract   : ∀ {A}   →  W A → A
    extend    : ∀ {A B} → (W A → B) → W A → W B
    isComonad : IsComonad extract extend

  open IsComonad isComonad public

-- Comonad definition using fmap, extract and duplicate.
record IsComonad′ {W : Set → Set}
         (fmap      : ∀ {A B} → (A → B) → W A → W B)
         (extract   : ∀ {A}   → W A → A)
         (duplicate : ∀ {A}   → W A → W (W A)) : Set₁ where
  field
    fmap-id : ∀ {A} (x : W A) →
      fmap id x ≡ x
    fmap-∘  : ∀ {A B C} (f : B → C) (g : A → B) (x : W A) →
      fmap (f ∘ g) x ≡ fmap f (fmap g x)

    ext-outer : ∀ {A} (x : W A) →
      extract (duplicate x) ≡ x
    ext-inner : ∀ {A} (x : W A) →
      fmap extract (duplicate x) ≡ x
    dup-dup   : ∀ {A} (x : W A) →
      duplicate (duplicate x) ≡ fmap duplicate (duplicate x)

    dup-nat : ∀ {A B} (f : A → B) (x : W A) →
      fmap (fmap f) (duplicate x) ≡ duplicate (fmap f x)
    ext-nat : ∀ {A B} (f : A → B) (x : W A) →
      f (extract x) ≡ extract (fmap f x)

record Comonad′ (W : Set → Set) : Set₁ where
  field
    fmap      : ∀ {A B} → (A → B) → W A → W B
    extract   : ∀ {A}   → W A → A
    duplicate : ∀ {A}   → W A → W (W A)
    isComonad : IsComonad′ fmap extract duplicate

  open IsComonad′ isComonad public
