{-# OPTIONS --without-K #-}

module PropositionalTruncation where 
  open import Basics
  open import EqualityAndPaths

  module _ where
    private
      data #∥_∥ {i} (A : U i) : U i where
        #∣_∣ : A → #∥ A ∥
    ∥_∥ : ∀ {i} (A : U i) → U i
    ∥ A ∥ = #∥ A ∥

    ∣_∣ : 
      ∀ {i} {A : U i} → A → ∥ A ∥
    ∣ a ∣ = #∣ a ∣

    postulate
      -1-truncated : ∀ {i} {A : U i} → (a a′ : ∥ A ∥) → a ≈ a′
    
    ∥-∥-recursion : 
      ∀ {i j} {A : U i} (B : U j)
      → B is-a-proposition → (f : A → B)
      → (∥ A ∥ → B)
    ∥-∥-recursion {A} B B-is-a-proposition f (#∣ a ∣) = f(a)

    ∥-∥-compute-recursion : 
      ∀ {A : 𝒰₀} (B : 𝒰₀)
      → (B-is-a-proposition : B is-a-proposition) → (f : A → B)
      → (a : A) → ∥-∥-recursion B B-is-a-proposition f (∣ a ∣) ≈ f a
    ∥-∥-compute-recursion B B-is-a-proposition f a = refl

    ∥-∥-induction : 
      ∀ {A : 𝒰₀} {P : ∥ A ∥ → 𝒰₀} 
        (proposition : (x : ∥ A ∥) → P(x) is-a-proposition) 
        (true-on-constructed : (a : A) → P(∣ a ∣))
        → ((x : ∥ A ∥) → P x)
    ∥-∥-induction proposition true-on-constructed #∣ x ∣ = true-on-constructed x 

    ∥-∥-is-truncation : 
      ∀ {i} (A : U i) → ∥ A ∥ is-a-proposition
    ∥-∥-is-truncation A = λ a a′ → -1-truncated a a′

    ∥→_∥→ :
      ∀ {i j} {A : U i} {B : U j}
      → (A → B) → ∥ A ∥ → ∥ B ∥
    ∥→ f ∥→ = ∥-∥-recursion _ (∥-∥-is-truncation _) (λ a → ∣ (f a) ∣)

    open import Equivalences
    open import Univalence
    
    ∥≃_∥≃ :
      ∀ {i} {A : U i} {B : U i}
      → (A ≃ B) → ∥ A ∥ ≃ ∥ B ∥
    ∥≃ f ∥≃ = U-transport (∥_∥ ⁎ (univalence f))
    
    {-
    fill in the following, if needed
    postulate
      uniqueness-of-∥-∥-recursion : 
      uniqueness-of-∥-∥-induction : 
    -}

