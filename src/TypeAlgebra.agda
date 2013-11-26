module TypeAlgebra where

open import Algebra
  using (CommutativeSemiring)
open import Algebra.FunctionProperties
  using ()
open import Data.Empty
  using (⊥; ⊥-elim)
open import Data.Product as P
  using (_×_; _,_; ,_; <_,_>; proj₁; proj₂; swap)
open import Data.Sum as S
  using (_⊎_; [_,_]; inj₁; inj₂)
open import Data.Unit
  using (⊤)
open import Function
  using (_∘_; id)
open import Level
  using (_⊔_; Lift; lift; lower; suc)
open import Relation.Binary
  using (_Preserves₂_⟶_⟶_; IsEquivalence; Transitive)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; cong₂; refl; trans)

record _≅_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor iso
  field
    to   : A → B
    from : B → A

    to-from : ∀ {x} → to (from x) ≡ x
    from-to : ∀ {x} → from (to x) ≡ x

isEquivalence : ∀ {ℓ} → IsEquivalence {suc ℓ} _≅_
isEquivalence {ℓ} = record
  { refl  = iso id id refl refl
  ; sym   = λ { (iso t f tf ft) → iso f t ft tf }
  ; trans = ≅-trans
  }
  where
  ≅-trans : Transitive _≅_
  ≅-trans (iso t₁ f₁ tf₁ ft₁) (iso t₂ f₂ tf₂ ft₂) = iso
    (t₂ ∘ t₁)
    (f₁ ∘ f₂)
    (trans (cong t₂ tf₁) tf₂)
    (trans (cong f₁ ft₂) ft₁)

semiring : ∀ {ℓ} → CommutativeSemiring (suc ℓ) ℓ
semiring {ℓ} = record
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
        ; assoc   = ⊎-assoc
        ; ∙-cong  = ⊎-cong
        }
      ; identityˡ = ⊎-identityˡ
      ; comm      = ⊎-comm
      }
    ; *-isCommutativeMonoid = record
      { isSemigroup = record
        { isEquivalence = isEquivalence
        ; assoc   = ×-assoc
        ; ∙-cong  = ×-cong
        }
      ; identityˡ = ×-identityˡ
      ; comm      = ×-comm
      }
    ; distribʳ = distribʳ
    ; zeroˡ    = zeroˡ
    }
  }
  where
  open Algebra.FunctionProperties (_≅_ {a = ℓ})

  ⊎-assoc : Associative _⊎_
  ⊎-assoc _ _ _ = iso
    [ [ inj₁ , inj₂ ∘ inj₁ ] , inj₂ ∘ inj₂ ]
    [ inj₁ ∘ inj₁ , [ inj₁ ∘ inj₂ , inj₂ ] ]
    (λ { {inj₁ _}        → refl
       ; {inj₂ (inj₁ _)} → refl
       ; {inj₂ (inj₂ _)} → refl
       })
    (λ { {inj₁ (inj₁ _)} → refl
       ; {inj₁ (inj₂ _)} → refl
       ; {inj₂ _}        → refl
       })

  ⊎-cong : _⊎_ Preserves₂ _≅_ ⟶ _≅_ ⟶ _≅_
  ⊎-cong (iso t₁ f₁ tf₁ ft₁) (iso t₂ f₂ tf₂ ft₂) = iso
    (S.map t₁ t₂)
    (S.map f₁ f₂)
    (λ { {inj₁ _} → cong inj₁ tf₁
       ; {inj₂ _} → cong inj₂ tf₂
       })
    (λ { {inj₁ _} → cong inj₁ ft₁
       ; {inj₂ _} → cong inj₂ ft₂
       })

  ⊎-identityˡ : LeftIdentity (Lift ⊥) _⊎_
  ⊎-identityˡ _ = iso
    [ ⊥-elim ∘ lower , id ]
    inj₂
    refl
    (λ { {inj₁ (lift ())}
       ; {inj₂ _} → refl
       })

  ⊎-comm : Commutative _⊎_
  ⊎-comm _ _ = iso
    [ inj₂ , inj₁ ]
    [ inj₂ , inj₁ ]
    (λ { {inj₁ _} → refl
       ; {inj₂ _} → refl
       })
    (λ { {inj₁ _} → refl
       ; {inj₂ _} → refl
       })

  ×-assoc : Associative _×_
  ×-assoc _ _ _ = iso
    < proj₁ ∘ proj₁ , < proj₂ ∘ proj₁ , proj₂ > >
    < < proj₁ , proj₁ ∘ proj₂ > , proj₂ ∘ proj₂ >
    refl
    refl

  ×-cong : _×_ Preserves₂ _≅_ ⟶ _≅_ ⟶ _≅_
  ×-cong (iso t₁ f₁ tf₁ ft₁) (iso t₂ f₂ tf₂ ft₂) = iso
    (P.map t₁ t₂)
    (P.map f₁ f₂)
    (cong₂ _,_ tf₁ tf₂)
    (cong₂ _,_ ft₁ ft₂)

  ×-identityˡ : LeftIdentity (Lift ⊤) _×_
  ×-identityˡ _ = iso
    proj₂
    ,_
    refl
    refl

  ×-comm : Commutative _×_
  ×-comm _ _ = iso
    swap
    swap
    refl
    refl

  distribʳ : _×_ DistributesOverʳ _⊎_
  distribʳ _ _ _ = iso
    (λ { (inj₁ y , x) → inj₁ (y , x)
       ; (inj₂ z , x) → inj₂ (z , x)
       })
    (λ { (inj₁ (y , x)) → inj₁ y , x
       ; (inj₂ (z , x)) → inj₂ z , x
       })
    (λ { {inj₁ _} → refl
       ; {inj₂ _} → refl
       })
    (λ { {inj₁ _ , _} → refl
       ; {inj₂ _ , _} → refl
       })

  zeroˡ : LeftZero (Lift ⊥) _×_
  zeroˡ _ = iso
    proj₁
    (⊥-elim ∘ lower)
    (λ { {lift ()}
       })
    (λ { {lift () , _ }
       })
