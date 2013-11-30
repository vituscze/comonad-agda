------------------------------------------------------------------------
-- The definitions from Comonad.Definition are indeed equivalent.
--
-- Sometimes, one of the definitions is easier to implement and this
-- gives us the ability to define comonad either way and get the
-- other one for free.
------------------------------------------------------------------------

module Comonad.Equivalence where

open import Function
  using (_∘_; _$_; flip; id)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; refl; sym; trans)

open import Category
  using (Category)
open import Comonad.Definition
  using (Comonad; module Comonad; Comonad′; module Comonad′)
open import FunExt
  using (ext)

-- (fmap, extract, duplicate) comonad derived from (extract, extend) comonad.
comonad→comonad′ : ∀ {W} → Comonad W → Comonad′ W
comonad→comonad′ comonad = record
  { fmap      = λ f → extend (f ∘ extract)
  ; extract   = extract
  ; duplicate = extend id
  ; isComonad = record
    { fmap-id   = extract-idʳ
    ; fmap-∘    = λ f g _ →
        trans (cong (flip extend _)
                (ext (cong f ∘ sym ∘ extract-idˡ (g ∘ extract)))) $
              (sym (extend-asso (f ∘ extract) (g ∘ extract) _))
    ; ext-outer = extract-idˡ id
    ; ext-inner = λ _ →
        trans (extend-asso (extract ∘ extract) id _) $
        trans (cong (flip extend _)
                (ext (cong extract ∘ extract-idˡ _))) $
              (extract-idʳ _)
    ; dup-dup   = λ _ →
        trans (extend-asso id id _) $
        trans (cong (flip extend _)
                (ext (cong (extend id) ∘ sym ∘ extract-idˡ id))) $
              (sym (extend-asso (extend id ∘ extract) id _))
    ; ext-nat   = λ _ → sym ∘ extract-idˡ _
    ; dup-nat   = λ f _ →
        trans (extend-asso (extend (f ∘ extract) ∘ extract) id _) $
        trans (cong (flip extend _)
                (ext (cong (extend (f ∘ extract)) ∘ extract-idˡ id))) $
              (sym (extend-asso id (f ∘ extract) _))
    }
  }
  where
  open Comonad comonad

-- (extract, extend) comonad derived from (fmap, extract, duplicate) comonad.
comonad′→comonad : ∀ {W} → Comonad′ W → Comonad W
comonad′→comonad comonad = record
  { extract   = extract
  ; extend    = λ f → fmap f ∘ duplicate
  ; isComonad = record
    { extract-idʳ = ext-inner
    ; extract-idˡ = λ f _ →
        trans (sym (ext-nat f (duplicate _))) $
              (cong f (ext-outer _))
    ; extend-asso = λ f g _ →
        trans (cong (fmap f) (sym (dup-nat g (duplicate _)))) $
        trans (cong (fmap f ∘ fmap (fmap g)) (dup-dup _)) $
        trans (sym (fmap-∘ f (fmap g) _)) $
              (sym (fmap-∘ (f ∘ fmap g) duplicate _))
    }
  }
  where
  open Comonad′ comonad

-- comonad→comonad′ and comonad′→comonad form an isomorphism with regards
-- to extract and extend operations.
module Comonad-Id {W : Set → Set} (comonad : Comonad W) where
  open Comonad comonad
  open Comonad (comonad′→comonad (comonad→comonad′ comonad))
    using ()
    renaming (extract to extract′; extend to extend′)

  id-extract : ∀ {A} (x : W A) →
    extract′ x ≡ extract x
  id-extract _ = refl

  id-extend : ∀ {A B} (f : W A → B) (x : W A) →
    extend′ f x ≡ extend f x
  id-extend f _ =
    trans (extend-asso (f ∘ extract) id _) $
          (cong (flip extend _) (ext (cong f ∘ extract-idˡ id)))

-- comonad′→comonad and comonad→comonad′ form an isomorphism with regards
-- to fmap, extract and duplicate operations.
module Comonad′-Id {W : Set → Set} (comonad : Comonad′ W) where
  open Comonad′ comonad
  open Comonad′ (comonad→comonad′ (comonad′→comonad comonad))
    using ()
    renaming (fmap to fmap′; extract to extract′; duplicate to duplicate′)

  id-fmap : ∀ {A B} (f : A → B) (x : W A) →
    fmap′ f x ≡ fmap f x
  id-fmap f _ =
    trans (fmap-∘ f extract _) $
          (cong (fmap f) (ext-inner _))

  id-extract : ∀ {A} (x : W A) →
    extract′ x ≡ extract x
  id-extract _ = refl

  id-duplicate : ∀ {A} (x : W A) →
    duplicate′ x ≡ duplicate x
  id-duplicate _ = fmap-id _
