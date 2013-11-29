module Lib.Data.Empty where

data ⊥ : Set where

⊥-elim : ∀ {a} {A : Set a} → ⊥ → A
⊥-elim ()
