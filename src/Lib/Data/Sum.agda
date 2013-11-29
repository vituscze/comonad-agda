module Lib.Data.Sum where

open import Lib.Function
open import Lib.Level

infixr 1 _⊎_

data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

[_,_] : ∀ {a b c} {A : Set a} {B : Set b} {C : A ⊎ B → Set c}
  (f : ∀ x → C (inj₁ x)) (g : ∀ x → C (inj₂ x)) →
  ∀ x → C x
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y

map : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
  (f : A → C) (g : B → D) → A ⊎ B → C ⊎ D
map f g = [ inj₁ ∘ f , inj₂ ∘ g ]
