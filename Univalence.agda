{-# OPTIONS --without-K #-}

module Univalence where 

  open import Basics public
  open import EqualityAndPaths public
  open import Equivalences public

  -- univalence
  postulate 
    univalence : ∀ {i} {A B : U i} → A ≃ B → A ≈ B
    
    univalence-is-an-equivalence : ∀ {i} {A B : U i} → (univalence {i} {A} {B}) is-quasiinverse-of U-transport

  univalence-as-equivalence : ∀ {i} {A B : U i} → (A ≈ B) ≃ (A ≃ B)
  univalence-as-equivalence = U-transport is-an-equivalence-because
    (has-left-inverse univalence by ∑π₁ univalence-is-an-equivalence
     and-right-inverse univalence by ∑π₂ univalence-is-an-equivalence)

  univalence-as-equivalence⁻¹ : ∀ {i} {A B : U i} → (A ≃ B) ≃ (A ≈ B)
  univalence-as-equivalence⁻¹ = univalence is-an-equivalence-because
    (has-left-inverse U-transport by (λ x → (∑π₂ univalence-is-an-equivalence) x ⁻¹)
     and-right-inverse U-transport by (λ x → (∑π₁ univalence-is-an-equivalence) x ⁻¹))

  propositions-are-equivalence-invariant :
    ∀ {P : 𝒰₀ → 𝒰₀} {A A′ : 𝒰₀}
    → (A ≃ A′) → P A → P A′
  propositions-are-equivalence-invariant e = transport _ (univalence e)

  the-proposition_is-equivalence-invariant-by-univalence_ :
    ∀ {i} (P : U i → U i) {A A′ : U i}
    → (A ≃ A′) → P A → P A′
  the-proposition P is-equivalence-invariant-by-univalence e = transport _ (univalence e)

  {- from HoTT-Agda: -}

  equivalence-induction : 
    ∀ {i j} (P : {A B : 𝒰 i} (f : A ≃ B) → 𝒰 j)
    → (p : (A : 𝒰 i) → P (id-as-equivalence {i} {A})) {A B : 𝒰 i} (f : A ≃ B)
    → P f
  equivalence-induction {i} {j} P p f =
    transport P ((∑π₂ univalence-is-an-equivalence) f ⁻¹) (aux P p (univalence f))
    where 
      aux : ∀ {j} (P : {A : 𝒰 i} {B : 𝒰 i} (f : A ≃ B) → 𝒰 j)
        (p : (A : 𝒰 i) → P (id-as-equivalence {_} {A})) {A B : 𝒰 i} (p : A ≈ B)
        → P (U-transport p)
      aux P d refl = d _
