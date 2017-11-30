{-# OPTIONS --without-K #-}

module LineGeometry where 
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Language
  open import Equivalences
  open import CommonEquivalences  
  open import EtaleMaps hiding (underlying-map-of)
  open import DependentTypes
  open import HomogeneousType
  open import FormalDisk
  open import FormalDiskBundle

  {-

   in this module, we use terminology
   suitable for a first order interpretation of ℑ
   (but the higher order case is not excluded by anything...)

  -}
  
  -- Some notions are defined relative to a 'line' 𝔸.
  -- For now, we just assume it is homogeneous
  module notions-relative-to-a-homogeneous-line (𝔸 : 𝒰) (𝔸′ : homogeneous-structure-on 𝔸) where
    open homogeneous-structure-on_ 𝔸′

    -- fix notation for the disk at the unit of 𝔸

    𝔻ₑ = 𝔻 𝔸 e

    τ : (x : 𝔸) → 𝔻 _ x → 𝔻ₑ
    τ = triviality-of-the-formal-disk-bundle-over-homogeneous-types.inverses-as-maps 𝔸′

    τ⁻¹ : (x : 𝔸) → 𝔻ₑ → 𝔻 _ x
    τ⁻¹ = triviality-of-the-formal-disk-bundle-over-homogeneous-types.equivalences-as-maps 𝔸′

    -- tangent vectors (jets) at a point are equivalence classes of curves through the point,
    -- where two curves are equivalent, if their derivatives agree.
    -- Since we are only interested in the derivate, we can also use maps
    -- f : 𝔻ₑ → X with f(∗)=x
    -- since those maps always factor over 𝔻_f(∗), we look at the more convenient type
    -- 𝔻ₑ → 𝔻ₓ
    
    vector-fields-on : 
      (X : 𝒰) → 𝒰
    vector-fields-on X  = (x : X) → 𝔻ₑ → 𝔻 _ x

    action-of-vector-fields-on-functions :
      ∀ {X : 𝒰}
      → vector-fields-on X → (f : X → 𝔸)
      → (X → (𝔻ₑ → 𝔻ₑ))
    action-of-vector-fields-on-functions χ f x = τ (f x) ∘ d f x ∘ χ x

    1-forms-on :
      (X : 𝒰) → 𝒰
    1-forms-on X = (x : X) → 𝔻 _ x → 𝔻ₑ

    Ω¹ = 1-forms-on

    d′ : ∀ {X : 𝒰}
      → (f : X → 𝔸)
      → Ω¹ X
    d′ f x = τ (f x) ∘ d f x

    evaluate : ∀ {X : 𝒰}
      → Ω¹ X → vector-fields-on X 
      → ((x : X) → 𝔻ₑ → 𝔻ₑ)
    evaluate ω χ x = (ω x) ∘ (χ x)


    pullback-of-forms :
      ∀ {X Y : 𝒰}
      → (φ : X → Y)
      → Ω¹ Y → Ω¹ X
    pullback-of-forms φ ω = λ x → ω (φ x) ∘ d φ x

    _⋆ = pullback-of-forms
    
