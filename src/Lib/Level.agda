module Lib.Level where

open import Agda.Primitive
  using    (Level; _⊔_)
  renaming (lzero to zero; lsuc to suc)
  public

record Lift {a ℓ} (A : Set a) : Set (a ⊔ ℓ) where
  constructor lift
  field
    lower : A

open Lift public
