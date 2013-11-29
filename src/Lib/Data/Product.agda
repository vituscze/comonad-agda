module Lib.Data.Product where

open import Lib.Function
open import Lib.Level

infixr 4 _,_
infix  4 ,_
infixr 2 _×_

record _×_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B

open _×_ public

,_ : ∀ {a b} {A : Set a} {B : Set b} {x : A} → B → A × B
,_ {x = x} y = x , y

swap : ∀ {a b} {A : Set a} {B : Set b} → A × B → B × A
swap (x , y) = y , x

<_,_> : ∀ {a b c} {A : Set a} {B : A → Set b} {C : A → Set c}
  (f : ∀ x → B x) (g : ∀ x → C x) → ∀ x → B x × C x
< f , g > x = f x , g x

map : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
  (f : A → C) (g : B → D) → A × B → C × D
map f g = < f ∘ proj₁ , g ∘ proj₂ >
