module Lib.PropositionalEquality where

open import Lib.Level

infix 4 _≡_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

sym : ∀ {a} {A : Set a} {x y : A} →
  x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {a} {A : Set a} {x y z : A} →
  x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {a b} {A : Set a} {B : Set b} {x y : A}
  (f : A → B) → x ≡ y → f x ≡ f y
cong _ refl = refl

cong₂ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} {x y : A} {u v : B} →
  (f : A → B → C) → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ _ refl refl = refl

Extensionality : ∀ a b → Set _
Extensionality a b = {A : Set a} {B : A → Set b}
  {f g : ∀ a → B a} → (∀ x → f x ≡ g x) → f ≡ g
