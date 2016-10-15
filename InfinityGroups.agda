{-# OPTIONS --without-K #-}

module InfinityGroups where 
  open import Basics
  open import EqualityAndPaths
  open import Fiber
  open import OneImage

  Ω : ∀ (X : U₀) (x₀ : X) → U₀
  Ω X x₀ = (x₀ ≈ x₀)

  -- Δ(g,h):=g•h⁻¹
  ∞-group-Δ : ∀ (BG : U₀) (e : BG)
              → Ω BG e × Ω BG e → Ω BG e
  ∞-group-Δ BG e (γ , η) = γ • η ⁻¹

  BAut : (A : U₀) → U₁
  BAut A = 1-image {_} {_} {One} {U₀} (λ ∗ → A)

  ι-BAut : (A : U₀) → BAut A → U₀
  ι-BAut A = ι-im₁ (λ ∗ → A)

  ι-BAut-is-1-mono : ∀ {A : U₀} → (ι-BAut A) is-1-mono
  ι-BAut-is-1-mono {A} = ι-im₁-is-1-mono (λ ∗₃ → A)

  BO1 : U₀
  BO1 = Bool

  module kernel (BG : U₀) (eG : BG) (BH : U₀) (eH : BH) (Bφ : BG → BH) where
      delooping = fiber-of Bφ at eH
