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


  -- Some notions are defined relative to a 'line' 𝔸.
  -- For now, we just assume it is homogeneous
  module notions-relative-to-a-homogeneous-line (𝔸 : 𝒰) (𝔸′ : homogeneous-structure-on 𝔸) where
    open homogeneous-structure-on_ 𝔸′

    -- fix notation for the disk at the unit of 𝔸

    𝔻ₑ = 𝔻 𝔸 e

    -- tangent vectors (or jets?) at a point are equivalence classes of curves through the point,
    -- where two curves are equivalent, if their derivatives agree.
    -- Since we are only interested in the derivate, we can also use maps
    -- f : 𝔻ₑ → X with f(∗)=x
    -- since those maps always factor over 𝔻_f(∗), we look at the more convenient type
    -- 𝔻ₑ → 𝔻ₓ
    
    Γ⟨T∞_⟩ : 
      (X : 𝒰) → 𝒰
    Γ⟨T∞ X ⟩ = (x : X) → 𝔻ₑ → 𝔻 _ x
    
    Γ⟨T∞∗_⟩  : 
      (X : 𝒰) → 𝒰
    Γ⟨T∞∗ X ⟩ = (x : X) → 𝔻 _ x → 𝔻ₑ


    eval : ∀ {X : 𝒰}
      → Γ⟨T∞∗ X ⟩ → Γ⟨T∞ X ⟩ → ((x : X) → 𝔻ₑ → 𝔻ₑ)
    eval ω χ x = (ω x) ∘ (χ x)
