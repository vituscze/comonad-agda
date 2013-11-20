open import Comonad.Definition

module Comonad.Cokleisli {W : Set → Set} (comonad : Comonad W) where

open import Function
open import Relation.Binary.PropositionalEquality

open import Category
open import FunExt

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
