{-# OPTIONS --without-K #-}

module InfinityGroups where 
  open import Basics
  open import EqualityAndPaths
  open import Equivalences
  open import Homotopies
  open import FunctionExtensionality
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
    -- discontinued...
      
  module equivalent-spaces-have-equivalent-BAut
    {A B : U₀} (f : A ≃ B) where
    -- univalence should not be necessary...

    open import Univalence

    equivalence : BAut A ≃ BAut B
    equivalence = transport-as-equivalence (λ X → BAut X) (univalence f)

    compute-transport-of-dependent-function-type :
      ∀ {A B : U₀} {P : (X : U₀) → U₁} (Q : (X : U₀) → ((P X) → U₀))
      → (γ : A ≈ B)
      → (f : P A → U₀) → f ∘ (transport P (γ ⁻¹)) ≈ transport _ γ f
    compute-transport-of-dependent-function-type _ refl _  = refl


    φ = underlying-map-of equivalence
    φ⁻¹ = left-inverse-of-the-equivalence equivalence
    φ⁻¹∘φ≈id : φ⁻¹ ∘ φ ≈ id
    φ⁻¹∘φ≈id = fun-ext (unit-of-the-equivalence equivalence)

    homotopy : ι-BAut A ⇒ ι-BAut B ∘ φ
    homotopy = equality-to-homotopy
       (ι-BAut A
      ≈⟨ (λ x → ι-BAut A ∘ x) ⁎ φ⁻¹∘φ≈id ⁻¹ ⟩
       ι-BAut A ∘ φ⁻¹ ∘ φ
      ≈⟨ (λ x → x ∘ φ) ⁎
           compute-transport-of-dependent-function-type ι-BAut (univalence f)
           (ι-BAut A) ⟩
       transport (λ z → BAut z → U₀) (univalence f) (ι-BAut A) ∘ φ
      ≈⟨ (λ x → x ∘ φ) ⁎ apd _ ι-BAut (univalence f) ⟩
       ι-BAut B ∘ φ
      ≈∎)

