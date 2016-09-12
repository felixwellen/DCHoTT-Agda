{-# OPTIONS --without-K #-}

module InfinityGroups where 
  open import Basics
  open import EqualityAndPaths



  Ω : ∀ (X : U₀) (x₀ : X) → U₀
  Ω X x₀ = (x₀ ≈ x₀)

  -- Δ(g,h):=g•h⁻¹
  ∞-group-Δ : ∀ (BG : U₀) (e : BG)
              → Ω BG e × Ω BG e → Ω BG e
  ∞-group-Δ BG e (γ , η) = γ • η ⁻¹
