------------------------------------------------------------------------
-- Function extensionality postulate.
------------------------------------------------------------------------

module FunExt where

open import Level
  using (zero)
open import Relation.Binary.PropositionalEquality
  using (Extensionality)

postulate
  ext : Extensionality zero zero
