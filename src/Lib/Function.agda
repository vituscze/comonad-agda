module Lib.Function where

infixr 9 _∘_
infixr 0 _$_

_∘_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
  (f : ∀ {x} (y : B x) → C x y) (g : ∀ x → B x) →
  ∀ x → C x (g x)
(f ∘ g) x = f (g x)

_$_ : ∀ {a b} {A : Set a} {B : A → Set b}
  (f : ∀ x → B x) →
  ∀ x → B x
f $ x = f x

id : ∀ {a} {A : Set a} → A → A
id x = x

flip : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c}
  (f : ∀ x y → C x y) →
  ∀ y x → C x y
flip f y x = f x y
