{-# OPTIONS --without-K #-}

module InfinityGroups where 
  open import Basics
  open import EqualityAndPaths
  open import Equivalences
  open import Homotopies
  open import PropositionalTruncation
  open import FunctionExtensionality
  open import Fiber
  open import Image

  Ω : ∀ (X : 𝒰₀) (x₀ : X) → 𝒰₀
  Ω X x₀ = (x₀ ≈ x₀)

  -- Δ(g,h):=g•h⁻¹
  ∞-group-Δ : ∀ (BG : 𝒰₀) (e : BG)
              → Ω BG e × Ω BG e → Ω BG e
  ∞-group-Δ BG e (γ , η) = γ • η ⁻¹

  BAut : (A : 𝒰₀) → U₁
  BAut A = image {_} {_} {𝟙} {𝒰₀} (λ ∗ → A)

  ι-BAut : (A : 𝒰₀) → BAut A → 𝒰₀
  ι-BAut A = ι-im₁ (λ ∗ → A)

  ι-BAut-is-injective : ∀ {A : 𝒰₀} → (ι-BAut A) is-injective
  ι-BAut-is-injective {A} = ι-im₁-is-injective (λ ∗₃ → A)

  universal-family-over-BAut′_ :
    (F : 𝒰₀) → (BAut F → 𝒰₀)
  (universal-family-over-BAut′ F) (F′ , p) = F′

  universal-family-over-BAut_ :
    (F : 𝒰₀) → 𝒰₁
  universal-family-over-BAut F = ∑ (universal-family-over-BAut′ F)
  
  -- the 'unit', i.e. 'refl {e-BAut A}' is the unit of 'Aut A'
  e-BAut : (A : 𝒰₀) → BAut A
  e-BAut A = (A , ∣ (∗ , refl) ∣ )

  BO1 : 𝒰₀
  BO1 = Bool

      
  module equivalent-spaces-have-equivalent-BAut
    {A B : 𝒰₀} (f : A ≃ B) where
    -- univalence should not be necessary...

    open import Univalence

    equivalence : BAut A ≃ BAut B
    equivalence = transport-as-equivalence (λ X → BAut X) (univalence f)

    compute-transport-of-dependent-function-type :
      ∀ {A B : 𝒰₀} {P : (X : 𝒰₀) → U₁} (Q : (X : 𝒰₀) → ((P X) → 𝒰₀))
      → (γ : A ≈ B)
      → (f : P A → 𝒰₀) → f ∘ (transport P (γ ⁻¹)) ≈ transport _ γ f
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
       transport (λ z → BAut z → 𝒰₀) (univalence f) (ι-BAut A) ∘ φ
      ≈⟨ (λ x → x ∘ φ) ⁎ apd _ ι-BAut (univalence f) ⟩
       ι-BAut B ∘ φ
      ≈∎)

