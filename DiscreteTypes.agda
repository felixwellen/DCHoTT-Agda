{-# OPTIONS --without-K #-}


{-
  This is part of an attempt to formalize Mike Shulman's
  real cohesion paper 
  (chapter 9, https://arxiv.org/abs/1509.07584 [1]).
  We do not work with the dedekind reals, but with a more
  abstract affine line object called '𝔸'
-}

module DiscreteTypes where
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Equivalences
  open import CommonEquivalences
  open import HalfAdjointEquivalences
  open import FunctionExtensionality
  open import Flat renaming (_is-discrete to _is-crisply-discrete)
  open import PostulateAffineLine


  _is-discrete : ∀ (A : 𝒰₀) → 𝒰₀
  A is-discrete = const {𝔸} {A} is-an-equivalence

  const-as-equivalence :
    ∀ {A : 𝒰₀} → A is-discrete → A ≃ (𝔸 → A)
  const-as-equivalence A-is-discrete = const is-an-equivalence-because A-is-discrete
  
  conclude-equality-of-values-from-discreteness :
    ∀ {A : 𝒰₀}
    → A is-discrete
    → (γ : 𝔸 → A) → (x y : 𝔸) → γ x ≈ γ y
  conclude-equality-of-values-from-discreteness
    (has-left-inverse _ by lp and-right-inverse r by rp) γ x y =
      (λ f → f x) ⁎ (rp γ) • (λ f → f y) ⁎ (rp γ) ⁻¹

  𝒰♭ = ∑ λ (A : 𝒰₀) → A is-discrete
  Π♭′ : ∀ {A : 𝒰₀} → (P : A → 𝒰♭) → 𝒰₀
  Π♭′ P = Π λ (x : _) → ∑π₁ (P x)

  Π-preserves-discreteness :
    ∀ {A : 𝒰₀} (P : A → 𝒰♭)
    → (Π♭′ P) is-discrete
  Π-preserves-discreteness {A} P =
    let
      φ : (𝔸 → Π♭′ P) ≃ (Π λ x → (𝔸 → ∑π₁ (P x)))
      φ = (λ s → (λ x a → s a x))
        is-an-equivalence-because
        (has-left-inverse (λ z z₁ a → z a z₁) by (λ a → refl)
        and-right-inverse (λ z z₁ a → z a z₁) by (λ a → refl))

      const-inverse-at : (x : A) → (𝔸 → ∑π₁ (P x)) → ∑π₁ (P x)
      const-inverse-at x = inverse-of _ given-by (∑π₂ (P x))

      right-invertible-at : (x : A) → const ∘ const-inverse-at x ⇒ id
      right-invertible-at x = const is-right-invertible-by (∑π₂ (P x))

      left-invertible-at : (x : A) → const-inverse-at x ∘ const ⇒ id
      left-invertible-at x = const is-left-invertible-by (∑π₂ (P x))

      ψ : (Π λ x → ∑π₁ (P x)) ≃ha (Π λ x → (𝔸 → ∑π₁ (P x)))
      ψ = construct-half-adjoint
            (λ s → (λ a → const (s a)))
            (λ s′ a → const-inverse-at a (s′ a))
            (λ s → fun-ext (λ a → left-invertible-at a (s a)))
            (λ s′ → fun-ext (λ a → right-invertible-at a (s′ a)))

      φ⁻¹∘ψ : Π♭′ P ≃ (𝔸 → Π♭′ P) 
      φ⁻¹∘ψ = (φ ⁻¹≃) ∘≃ half-adjoint-equivalences-to-equivalences ψ
      
    in the-map const is-an-equivalence-since-it-is-homotopic-to-the-equivalence
      φ⁻¹∘ψ by (λ s → refl) 

  Π♭ : ∀ {A : 𝒰₀} → (P : A → 𝒰♭) → 𝒰♭
  Π♭ P = (Π♭′ P) , (Π-preserves-discreteness P)
  
  ≈-preserves-discreteness :
    ∀ {A : 𝒰₀} {a a′ : A}
    → A is-discrete → (a ≈ a′) is-discrete
  ≈-preserves-discreteness {A} {a} {a′} A-is-discrete =
    let
      ψ : (a ≈ a′) ≃ (𝔸 → (a ≈ a′))
      ψ = (a ≈ a′)
         ≃⟨ (const-as-equivalence A-is-discrete) ∗≃ ⟩ 
          (const a ≈ const a′)
         ≃⟨ {!!} ⟩
          (𝔸 → (a ≈ a′))
         ≃∎
    in the-map const is-an-equivalence-since-it-is-homotopic-to-the-equivalence
     ψ by (λ x → {!!}) 

