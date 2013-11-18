module TypeAlgebra where

open import Algebra
  using (CommutativeSemiring)
open import Data.Empty
  using (⊥)
open import Data.Product
  using (_×_; _,_)
open import Data.Sum
  using (_⊎_; inj₁; inj₂)
open import Data.Unit
  using (⊤)
open import Function
  using (_∘_; id)
open import Level
open import Relation.Binary
  using (IsEquivalence; Rel)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂)

infix 1 _≅_

record _≅_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor iso
  field
    to   : A → B
    from : B → A

    to-from : ∀ x → to (from x) ≡ x
    from-to : ∀ x → from (to x) ≡ x

isEquivalence : ∀ {ℓ} → IsEquivalence {suc ℓ} _≅_
isEquivalence {ℓ} = record
  { refl  = iso id id (λ _ → refl) (λ _ → refl)
  ; sym   = λ { (iso t f tf ft) → iso f t ft tf }
  ; trans = trans′
  }
  where
  trans′ : ∀ {A B C : Set ℓ} → A ≅ B → B ≅ C → A ≅ C
  trans′ (iso to₁ from₁ to-from₁ from-to₁) (iso to₂ from₂ to-from₂ from-to₂)
    = iso (to₂ ∘ to₁) (from₁ ∘ from₂) pf₁ pf₂
    where
    pf₁ : ∀ x → to₂ (to₁ (from₁ (from₂ x))) ≡ x
    pf₁ x rewrite to-from₁ (from₂ x) = to-from₂ x

    pf₂ : ∀ x → from₁ (from₂ (to₂ (to₁ x))) ≡ x
    pf₂ x rewrite from-to₂ (to₁ x) = from-to₁ x

typeSemiring : ∀ {ℓ} → CommutativeSemiring (suc ℓ) ℓ
typeSemiring {ℓ} = record
  { Carrier = Set ℓ
  ; _≈_ = _≅_
  ; _+_ = _⊎_
  ; _*_ = _×_
  ; 0#  = Lift ⊥
  ; 1#  = Lift ⊤
  ; isCommutativeSemiring = record
    { +-isCommutativeMonoid = record
      { isSemigroup = record
        { isEquivalence = isEquivalence
        ; assoc  = λ _ _ _ → ⊎-assoc
        ; ∙-cong = ⊎-cong
        }
      ; identityˡ = λ _ → ⊎-⊥-id
      ; comm      = λ _ _ → ⊎-comm
      }
    ; *-isCommutativeMonoid = record
      { isSemigroup = record
        { isEquivalence = isEquivalence
        ; assoc  = λ _ _ _ → ×-assoc
        ; ∙-cong = ×-cong
        }
      ; identityˡ = λ _ → ×-⊤-id
      ; comm      = λ _ _ → ×-comm
      }
    ; distribʳ = λ _ _ _ → distrib
    ; zeroˡ    = λ _ → zeroˡ
    }
  }
  where
  ⊎-assoc : {A B C : Set ℓ} → (A ⊎ B) ⊎ C ≅ A ⊎ B ⊎ C
  ⊎-assoc {A} {B} {C} = iso to from to-from from-to
    where
    to : (A ⊎ B) ⊎ C → A ⊎ B ⊎ C
    to (inj₁ (inj₁ x)) = inj₁ x
    to (inj₁ (inj₂ x)) = inj₂ (inj₁ x)
    to (inj₂ x)        = inj₂ (inj₂ x)

    from : A ⊎ B ⊎ C → (A ⊎ B) ⊎ C
    from (inj₁ x)        = inj₁ (inj₁ x)
    from (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
    from (inj₂ (inj₂ x)) = inj₂ x

    to-from : ∀ x → to (from x) ≡ x
    to-from (inj₁ x) = refl
    to-from (inj₂ (inj₁ x)) = refl
    to-from (inj₂ (inj₂ x)) = refl

    from-to : ∀ x → from (to x) ≡ x
    from-to (inj₁ (inj₁ x)) = refl
    from-to (inj₁ (inj₂ x)) = refl
    from-to (inj₂ x)        = refl

  ⊎-cong : {A B C D : Set ℓ} → A ≅ C → B ≅ D → A ⊎ B ≅ C ⊎ D
  ⊎-cong {A} {B} {C} {D} (iso to₁ from₁ to-from₁ from-to₁) (iso to₂ from₂ to-from₂ from-to₂)
    = iso to from to-from from-to
    where
    to : A ⊎ B → C ⊎ D
    to (inj₁ a) = inj₁ (to₁ a)
    to (inj₂ b) = inj₂ (to₂ b)

    from : C ⊎ D → A ⊎ B
    from (inj₁ c) = inj₁ (from₁ c)
    from (inj₂ d) = inj₂ (from₂ d)

    to-from : ∀ x → to (from x) ≡ x
    to-from (inj₁ c) rewrite to-from₁ c = refl
    to-from (inj₂ d) rewrite to-from₂ d = refl

    from-to : ∀ x → from (to x) ≡ x
    from-to (inj₁ a) rewrite from-to₁ a = refl
    from-to (inj₂ b) rewrite from-to₂ b = refl

  ⊎-⊥-id : {A : Set ℓ} → Lift {ℓ = ℓ} ⊥ ⊎ A ≅ A
  ⊎-⊥-id {A} = iso to from (λ _ → refl) from-to
    where
    to : Lift {ℓ = ℓ} ⊥ ⊎ A → A
    to (inj₁ (lift ()))
    to (inj₂ a) = a

    from : A → Lift {ℓ = ℓ} ⊥ ⊎ A
    from a = inj₂ a

    from-to : ∀ x → from (to x) ≡ x
    from-to (inj₁ (lift ()))
    from-to (inj₂ a) = refl

  ⊎-comm : {A B : Set ℓ} → A ⊎ B ≅ B ⊎ A
  ⊎-comm = iso swap swap swap-id swap-id
    where
    swap : {C D : Set ℓ} → C ⊎ D → D ⊎ C
    swap (inj₁ c) = inj₂ c
    swap (inj₂ d) = inj₁ d

    swap-id : {C D : Set ℓ} (x : C ⊎ D) → swap (swap x) ≡ x
    swap-id (inj₁ c) = refl
    swap-id (inj₂ d) = refl

  ×-assoc : {A B C : Set ℓ} → (A × B) × C ≅ A × B × C
  ×-assoc = iso (λ {((a , b) , c) → a , b , c}) (λ {(a , b , c) → (a , b) , c})
    (λ _ → refl) (λ _ → refl)

  ×-cong : {A B C D : Set ℓ} → A ≅ C → B ≅ D → A × B ≅ C × D
  ×-cong {A} {B} {C} {D} (iso to₁ from₁ to-from₁ from-to₁) (iso to₂ from₂ to-from₂ from-to₂)
    = iso to from to-from from-to
    where
    to : A × B → C × D
    to (a , b) = to₁ a , to₂ b

    from : C × D → A × B
    from (c , d) = from₁ c , from₂ d

    to-from : ∀ x → to (from x) ≡ x
    to-from (c , d) rewrite to-from₁ c | to-from₂ d = refl

    from-to : ∀ x → from (to x) ≡ x
    from-to (a , b) rewrite from-to₁ a | from-to₂ b = refl

  ×-⊤-id : {A : Set ℓ} → Lift {ℓ = ℓ} ⊤ × A ≅ A
  ×-⊤-id = iso (λ {(_ , a) → a}) (λ a → lift _ , a) (λ _ → refl) (λ _ → refl)

  ×-comm : {A B : Set ℓ} → A × B ≅ B × A
  ×-comm = iso (λ {(a , b) → b , a}) (λ {(b , a) → a , b}) (λ _ → refl) (λ _ → refl)

  distrib : {A B C : Set ℓ} → (A ⊎ B) × C ≅ A × C ⊎ B × C
  distrib {A} {B} {C} = iso to from to-from from-to
    where
    to : (A ⊎ B) × C → A × C ⊎ B × C
    to (inj₁ a , c) = inj₁ (a , c)
    to (inj₂ b , c) = inj₂ (b , c)

    from : A × C ⊎ B × C → (A ⊎ B) × C
    from (inj₁ (a , c)) = inj₁ a , c
    from (inj₂ (b , c)) = inj₂ b , c

    to-from : ∀ x → to (from x) ≡ x
    to-from (inj₁ (a , c)) = refl
    to-from (inj₂ (b , c)) = refl

    from-to : ∀ x → from (to x) ≡ x
    from-to (inj₁ a , c) = refl
    from-to (inj₂ b , c) = refl

  zeroˡ : {A : Set ℓ} → Lift {ℓ = ℓ} ⊥ × A ≅ Lift {ℓ = ℓ} ⊥
  zeroˡ = iso (λ {(lift () , _)}) (λ {(lift ())}) (λ {(lift ())}) (λ {(lift (), _)})