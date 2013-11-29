module Lib.Data.List where

infixr 5 _∷_

data List {a} (A : Set a) : Set a where
  []  :              List A
  _∷_ : A → List A → List A

map : ∀ {a b} {A : Set a} {B : Set b}
  (f : A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs
