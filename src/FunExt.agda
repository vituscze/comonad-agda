------------------------------------------------------------------------
-- Function extensionality postulate.
------------------------------------------------------------------------

module FunExt where

open import Lib.Level
  using (zero)
open import Lib.Relation.Binary.PropositionalEquality
  using (Extensionality)

postulate
  ext : Extensionality zero zero
