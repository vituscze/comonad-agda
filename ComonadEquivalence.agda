module ComonadEquivalence where

open import Function
open import Relation.Binary.PropositionalEquality

open import Category
open import ComonadDef
open import FunExt

comonad→comonad′ : ∀ {W} → Comonad W → Comonad′ W
comonad→comonad′ comonad = record
  { fmap      = λ f → extend (f ∘ extract)
  ; extract   = extract
  ; duplicate = extend id
  ; isComonad = record
    { fmap-id   = extract-idʳ
    ; fmap-∘    = λ f g _ →
        trans (cong (flip extend _)
                (ext (cong f ∘ sym ∘ extract-idˡ (g ∘ extract)))) $
              (sym (extend-asso (f ∘ extract) (g ∘ extract) _))
    ; ext-outer = extract-idˡ id
    ; ext-inner = λ _ →
        trans (extend-asso (extract ∘ extract) id _) $
        trans (cong (flip extend _)
                (ext (cong extract ∘ extract-idˡ _))) $
              (extract-idʳ _)
    ; dup-dup   = λ _ →
        trans (extend-asso id id _) $
        trans (cong (flip extend _)
                (ext (cong (extend id) ∘ sym ∘ extract-idˡ id))) $
              (sym (extend-asso (extend id ∘ extract) id _))
    ; ext-nat   = λ _ → sym ∘ extract-idˡ _
    ; dup-nat   = λ f _ →
        trans (extend-asso (extend (f ∘ extract) ∘ extract) id _) $
        trans (cong (flip extend _)
                (ext (cong (extend (f ∘ extract)) ∘ extract-idˡ id))) $
              (sym (extend-asso id (f ∘ extract) _))
    }
  }
  where
  open Comonad comonad

comonad′→comonad : ∀ {W} → Comonad′ W → Comonad W
comonad′→comonad comonad = record
  { extract   = extract
  ; extend    = λ f → fmap f ∘ duplicate
  ; isComonad = record
    { extract-idʳ = ext-inner
    ; extract-idˡ = λ f _ →
        trans (sym (ext-nat f (duplicate _))) $
              (cong f (ext-outer _))
    ; extend-asso = λ f g _ →
        trans (cong (fmap f) (sym (dup-nat g (duplicate _)))) $
        trans (cong (fmap f ∘ fmap (fmap g)) (dup-dup _)) $
        trans (sym (fmap-∘ f (fmap g) _)) $
              (sym (fmap-∘ (f ∘ fmap g) duplicate _))
    }
  }
  where
  open Comonad′ comonad

module Cokleisli {W : Set → Set} (comonad : Comonad W) where
  open Comonad comonad

  infixr 1 _⇒_

  _⇒_ : Set → Set → Set
  A ⇒ B = W A → B

  category : Category _⇒_
  category = record
    { _∘_ = λ f g → f ∘ extend g
    ; id  = extract
    ; isCategory = record
      { idʳ   = λ f     → ext (cong f ∘ extract-idʳ)
      ; idˡ   = λ f     → ext (extract-idˡ _)
      ; assoc = λ f g h → ext (cong f ∘ sym ∘ extend-asso g h)
      }
    }
