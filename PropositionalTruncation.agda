{-# OPTIONS --without-K #-}

module PropositionalTruncation where 
  open import Basics
  open import EqualityAndPaths

  module _ where
    private
      data #∥_∥ (A : U₀) : U₀ where
        #∣_∣ : A → #∥ A ∥
    ∥_∥ : (A : U₀) → U₀
    ∥ A ∥ = #∥ A ∥

    ∣_∣ : 
      ∀ {A : U₀} → A → ∥ A ∥
    ∣ a ∣ = #∣ a ∣

    postulate
      -1-truncated : ∀ {A : U₀} → (a a′ : ∥ A ∥) → a ≈ a′
    
    ∥-∥-recursion : ∀ {A : U₀} (B : U₀)
              → B is-a-proposition → (f : A → B)
              → (∥ A ∥ → B)
    ∥-∥-recursion {A} B B-is-a-proposition f (#∣ a ∣) = f(a)

    ∥-∥-induction : ∀ {A : U₀} {P : ∥ A ∥ → U₀} (true-on-constructed : (a : A) → P(∣ a ∣))
             → ((x : ∥ A ∥) → P x)
    ∥-∥-induction true-on-constructed #∣ x ∣ = true-on-constructed x 

    {-
    fill in the following, if needed
    postulate
      uniqueness-of-∥-∥-recursion : 
      uniqueness-of-∥-∥-induction : 
    -}

