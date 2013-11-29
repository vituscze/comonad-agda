module Comonad.Examples where

open import Lib.Algebra.Structures
  using (IsMonoid; module IsMonoid)
open import Lib.Data.List
  using ([]; _∷_; List; map)
open import Lib.Data.Product
  using (_×_; _,_; proj₁; proj₂)
open import Lib.Function
  using (_∘_; _$_; id)
open import Lib.Relation.Binary.PropositionalEquality
  using (_≡_; cong; refl)

open import Comonad.Definition
  using (Comonad; module Comonad)
open import FunExt
  using (ext)

--

Id : Set → Set
Id X = X

id-Comonad : Comonad Id
id-Comonad = record
  { extract   = id
  ; extend    = id
  ; isComonad = record
    { extract-idʳ = λ     _ → refl
    ; extract-idˡ = λ   _ _ → refl
    ; extend-asso = λ _ _ _ → refl
    }
  }

--

Store : Set → Set → Set
Store S A = (S → A) × S

store-Comonad : ∀ S → Comonad (Store S)
store-Comonad S = record
  { extract = λ {   (f , s) → f s }
  ; extend  = λ { g (f , s) → (λ s′ → g (f , s′)) , s }
  ; isComonad = record
    { extract-idʳ = λ     _ → refl
    ; extract-idˡ = λ   _ _ → refl
    ; extend-asso = λ _ _ _ → refl
    }
  }

--

Reader : Set → Set → Set
Reader M A = M → A

reader-Comonad : ∀ M (_∙_ : M → M → M) (ε : M) →
  IsMonoid _≡_ _∙_ ε → Comonad (Reader M)
reader-Comonad M _∙_ ε isMonoid = record
  { extract   = λ   f    → f ε
  ; extend    = λ g f m₁ → g λ m₂ → f (m₁ ∙ m₂)
  ; isComonad = record
    { extract-idʳ = λ     f →
                ext (cong f ∘ proj₂ identity)
    ; extract-idˡ = λ   g f →
        cong g (ext (cong f ∘ proj₁ identity))
    ; extend-asso = λ h g f →
        ext λ _ → cong h $
        ext λ _ → cong g $
        ext λ _ → cong f $
        assoc _ _ _
    }
  }
  where
  open IsMonoid isMonoid
    using (identity; assoc)

--

data _+_ (F G : Set → Set) (A : Set) : Set where
  left  : F A → (F + G) A
  right : G A → (F + G) A

+-elim : ∀ {F G A} {B : Set} → (F A → B) → (G A → B) → (F + G) A → B
+-elim f g (left  a) = f a
+-elim f g (right a) = g a

+-comonad : ∀ {F G} → Comonad F → Comonad G →
  Comonad (F + G)
+-comonad f g = record
  { extract   = +-elim F.extract G.extract
  ; extend    = λ h → +-elim
      (left  ∘ F.extend (h ∘ left ))
      (right ∘ G.extend (h ∘ right))
  ; isComonad = record
    { extract-idʳ = λ {     (left  _) → cong left  (F.extract-idʳ _)
                      ;     (right _) → cong right (G.extract-idʳ _)
                      }
    ; extract-idˡ = λ {   _ (left  _) → F.extract-idˡ _ _
                      ;   _ (right _) → G.extract-idˡ _ _
                      }
    ; extend-asso = λ { _ _ (left  _) → cong left  (F.extend-asso _ _ _)
                      ; _ _ (right _) → cong right (G.extend-asso _ _ _)
                      }
    }
  }
  where
  module F = Comonad f
  module G = Comonad g

--

Env : Set → Set → Set
Env E A = E × A

env-comonad : ∀ E → Comonad (Env E)
env-comonad E = record
  { extract   = proj₂
  ; extend    = λ { f (e , a) → e , f (e , a) }
  ; isComonad = record
    { extract-idʳ = λ     _ → refl
    ; extract-idˡ = λ   _ _ → refl
    ; extend-asso = λ _ _ _ → refl
    }
  }

--

data NonEmpty (A : Set) : Set where
  [_] : A → NonEmpty A
  _∷_ : A → NonEmpty A → NonEmpty A

nonEmpty-elim : ∀ {A} {P : NonEmpty A → Set} →
  (f : ∀ a {as} → P as → P (a ∷ as))
  (z : ∀ a → P [ a ]) →
  ∀ as → P as
nonEmpty-elim f z [ a ]    = z a
nonEmpty-elim f z (a ∷ as) = f a (nonEmpty-elim f z as)

nonEmpty-comonad : Comonad NonEmpty
nonEmpty-comonad = record
  { extract   =       nonEmpty-elim (λ a _ → a) id
  ; extend    = λ f → nonEmpty-elim
      (λ a {as} r → f (a ∷ as) ∷ r)
      (λ a        → [ f [ a ] ])
  ; isComonad = record
    { extract-idʳ =         nonEmpty-elim (λ _ → cong (_∷_ _)) (λ _ → refl)
    ; extract-idˡ = λ   _ → nonEmpty-elim (λ _ _ → refl)       (λ _ → refl)
    ; extend-asso = λ _ _ → nonEmpty-elim (λ _ → cong (_∷_ _)) (λ _ → refl)
    }
  }

--

Zipper : Set → Set
Zipper A = List A × A × List A

mapZ : ∀ {A B} → (A → B) → Zipper A → Zipper B
mapZ f (l , x , r) = map f l , f x , map f r

listZipper-comonad : Comonad Zipper
listZipper-comonad = record
  { extract   = extract
  ; extend    = extend
  ; isComonad = record
    { extract-idʳ = extract-idʳ
    ; extract-idˡ = extract-idˡ
    ; extend-asso = extend-asso
    }
  }
  where
  -- Comonad operations.
  before : ∀ {A} → Zipper A → List A
  before = proj₁

  after : ∀ {A} → Zipper A → List A
  after = proj₂ ∘ proj₂

  lefts : ∀ {A} → List A → A → List A → List (Zipper A)
  lefts []       x r = []
  lefts (l ∷ ls) x r = (ls , l , x ∷ r) ∷ lefts ls l (x ∷ r)

  rights : ∀ {A} → List A → A → List A → List (Zipper A)
  rights l x []       = []
  rights l x (r ∷ rs) = (x ∷ l , r , rs) ∷ rights (x ∷ l) r rs

  duplicate : ∀ {A} → Zipper A → Zipper (Zipper A)
  duplicate (l , x , r) = lefts l x r , (l , x , r) , rights l x r

  extract : ∀ {A} → Zipper A → A
  extract = proj₁ ∘ proj₂

  extend : ∀ {A B} → (Zipper A → B) → Zipper A → Zipper B
  extend f = mapZ f ∘ duplicate

  -- Lemmas.
  extract-left : ∀ {A} l (x : A) r →
    map extract (lefts l x r) ≡ l
  extract-left []      _ _ = refl
  extract-left (_ ∷ _) _ _ = cong (_∷_ _) (extract-left _ _ _)

  extract-right : ∀ {A} l (x : A) r →
    map extract (rights l x r) ≡ r
  extract-right _ _ []      = refl
  extract-right _ _ (_ ∷ _) = cong (_∷_ _) (extract-right _ _ _)

  asso-left : ∀ {A B C} (f : Zipper B → C) (g : Zipper A → B) l x r →
    let z = l , x , r
    in map f (before (duplicate (extend g z)))
     ≡ map (f ∘ extend g) (before (duplicate z))
  asso-left _ _ []      _ _ = refl
  asso-left _ _ (_ ∷ _) _ _ = cong (_∷_ _) (asso-left _ _ _ _ _)

  asso-right : ∀ {A B C} (f : Zipper B → C) (g : Zipper A → B) l x r →
    let z = l , x , r
    in map f (after (duplicate (extend g z)))
     ≡ map (f ∘ extend g) (after (duplicate z))
  asso-right _ _ _ _ []      = refl
  asso-right _ _ _ _ (_ ∷ _) = cong (_∷_ _) (asso-right _ _ _ _ _)

  -- Comonad laws.
  extract-idʳ : ∀ {A} (x : Zipper A) →
    extend extract x ≡ x
  extract-idʳ (l , x , r)
    rewrite extract-left l x r | extract-right l x r = refl

  extract-idˡ : ∀ {A B} (f : Zipper A → B) (x : Zipper A) →
    extract (extend f x) ≡ f x
  extract-idˡ _ _ = refl

  extend-asso : ∀ {A B C}
    (f : Zipper B → C) (g : Zipper A → B) (x : Zipper A) →
    extend f (extend g x) ≡ extend (f ∘ extend g) x
  extend-asso f g (l , x , r)
    rewrite asso-left f g l x r | asso-right f g l x r = refl
