{-# OPTIONS --without-K #-}

module S1 where 
  open import Basics 
  open import EqualityAndPaths
  open import Homotopies
  open import Equivalences
  open import FunctionExtensionality

  module _ where
    private
      data #S¹ : U₀ where
        #base : #S¹
    S¹ : U₀
    S¹ = #S¹

    base : S¹
    base = #base

    postulate
      loop : base ≈ base
    
    S¹-recursion : ∀ {i} {A : U i} 
              → (a⁎ : A) → (aₗ : a⁎ ≈ a⁎) 
              → (S¹ → A)
    S¹-recursion {i} {A} a⁎ aₗ #base = a⁎
    
    S¹-induction : ∀ {i} {P : S¹ → U i} 
                 → (p⁎ : P base) → (pₗ : transport P loop p⁎ ≈ p⁎) 
                 → ((x : S¹) →  P x)
    S¹-induction p⁎ pₗ #base = p⁎

    postulate
      uniqueness-of-S¹-recursion : ∀ {i} {A : U i} 
              → (a⁎ : A) → (aₗ : a⁎ ≈ a⁎) 
              → (S¹-recursion a⁎ aₗ) ⁎ loop ≈ aₗ
      uniqueness-of-S¹-induction : ∀ {i} {P : S¹ → U i} 
              → (p⁎ : P base) → (pₗ : transport P loop p⁎ ≈ p⁎) 
              → apd P (S¹-induction p⁎ pₗ) loop ≈ pₗ



    free-loops-in_ :
      ∀ (A : U₀)
      → U₀
    free-loops-in A = ∑ (λ (a : A) → a ≈ a)

    loop-to-map-from-S¹ :
      ∀ {A : U₀} {a : A}
      → a ≈ a → (S¹ → A)
    loop-to-map-from-S¹ γ =
      S¹-recursion _ γ

    map-from-S¹-to-loop :
      ∀ {A : U₀}
      → (l : S¹ → A) → l(base) ≈ l(base)
    map-from-S¹-to-loop l = l ⁎ loop


    free-loops-are-maps-from-S¹ :
      ∀ (A : U₀)
      → free-loops-in A ≃ (S¹ → A) 
    free-loops-are-maps-from-S¹ A =
      (λ {(above a is γ) → loop-to-map-from-S¹ γ })
        is-an-equivalence-because
        (has-left-inverse (λ l → ⟨ l base , l ⁎ loop ⟩∑)
          by (λ {(above a is γ) → (λ ξ → above a is ξ) ⁎ uniqueness-of-S¹-recursion a γ})
        and-right-inverse (λ l → ⟨ l base , l ⁎ loop ⟩∑)
          by (λ l → fun-ext (S¹-induction refl {!uniqueness-of-S¹-induction!})))
