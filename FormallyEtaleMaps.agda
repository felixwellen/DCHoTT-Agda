{-# OPTIONS --without-K #-}

module FormallyEtaleMaps where
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Equivalences renaming (underlying-map-of to underlying-map-of-the-equivalence)
  open import Pullback
  open import PullbackSquare
  open import DependentTypes
  open import Im
  open import Language

  _as-plain-map :
    ∀ {A B : 𝒰₀}
    → (f : A ≃ B) → (A → B)
  f as-plain-map = underlying-map-of-the-equivalence f

  -- X --→ ℑ X
  -- |      |
  -- f      ℑf
  -- ↓      ↓
  -- Y --→ ℑ Y

  _is-a-formally-étale-map : ∀ {X Y : 𝒰₀} (f : X → Y) → 𝒰₀
  f is-a-formally-étale-map =
    the-square-with-right (apply-ℑ-to-map f)
      bottom ℑ-unit
      top ℑ-unit
      left f
      commuting-by (naturality-of-ℑ-unit f)
     is-a-pullback-square

  -- this also follows from stuff in the proof of the triviality theorem
  equivalences-are-étale :
    ∀ {A B : 𝒰₀} (f : A ≃ B)
    → (f as-plain-map) is-a-formally-étale-map
  equivalences-are-étale {A} {B} f =
    let
      □ : pullback-square-with-right ℑ→ (f as-plain-map)
            bottom ℑ-unit
            top ℑ-unit
            left (f as-plain-map)
      □ = pullback-preserves-equivalences.reverse-statement
           (ℑ→ (f as-plain-map))
           ℑ-unit (applying-ℑ-preserves-equivalences (f as-plain-map) (proof-of-equivalency f) )
           ℑ-unit
           (f as-plain-map) (naturality-of-ℑ-unit (f as-plain-map))
           (proof-of-equivalency f)
    in the-induced-map-is-an-equivalence-by
     (the-induced-map-in □ is-an-equivalence)


  _─ét→_ : (A B : 𝒰₀) → 𝒰₀
  A ─ét→ B = ∑ (λ (f : A → B) → f is-a-formally-étale-map)

  _is-étale-because_ : {A B : U₀}
    → (f : A → B) → f is-a-formally-étale-map
    → (A ─ét→ B)
  f is-étale-because p = f , p

  id-as-étale-map :
    ∀ {A : 𝒰₀}
    → A ─ét→ A
  id-as-étale-map = (id , equivalences-are-étale id-as-equivalence)

  underlying-map-of :
    ∀ {A B : 𝒰₀}
    → (A ─ét→ B) → (A → B)
  underlying-map-of (f , _) = f

  _ét→ :
    ∀ {A B : 𝒰₀}
    → (A ─ét→ B) → (A → B)
  f ét→ = underlying-map-of f

  _$ét_ :
    ∀ {A B : 𝒰₀}
    → (A ─ét→ B) → A → B
  f $ét x = (f ét→) x

  _is-étale = _is-a-formally-étale-map

  pullback-square-of :
    ∀ {A B : 𝒰₀}
    → (f́ : A ─ét→ B)
    → pullback-square-with-right (ℑ→ (underlying-map-of f́))
        bottom ℑ-unit
        top ℑ-unit
        left (underlying-map-of f́)
  pullback-square-of (f , (the-induced-map-is-an-equivalence-by pullback-property)) =
    the-square-commuting-by (naturality-of-ℑ-unit f)
      and-inducing-an-equivalence-by pullback-property
