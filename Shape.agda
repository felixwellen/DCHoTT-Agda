{-# OPTIONS --without-K #-}


{-
  An attempt to write down the shape functor from Mike Shulman's
  real cohesion paper 
  (chapter 9, https://arxiv.org/abs/1509.07584).
-}

module Shape where
  open import Basics
  open import EqualityAndPaths

  module _ (𝔸 : 𝒰) where
    
    const : {X Y : 𝒰₀} → Y → (X → Y)
    const y₀ = λ _ → y₀
    
    private
      data #∫ (A : 𝒰₀) : 𝒰₀ where
        #σ : A → #∫ A
        #κ  : (𝔸 → #∫ A) → #∫ A
        #κ′ : (𝔸 → #∫ A) → #∫ A
        
    ∫ : (A : 𝒰₀) → 𝒰₀
    ∫ A = #∫ A

    module _ (A : 𝒰₀) where
      σ : A → ∫ A
      σ A = #σ A
    
      κ : (𝔸 → ∫ A) → ∫ A
      κ = #κ
    
      κ′ : (𝔸 → ∫ A) → ∫ A
      κ′ = #κ′

      postulate
        p1 : (γ : 𝔸 → ∫ A) → ((x : 𝔸) → γ x ≈ κ γ)
        p2 : (x : ∫ A) → x ≈ κ′ (const x)


      module _ (B : 𝒰₀) where
        ∫-recursion :
          (A → B) 
          → (κB : (𝔸 → B) → B)
          → (κ′B : (𝔸 → B) → B)
          → ((γ : 𝔸 → B) → ((x : 𝔸) → γ x ≈ κB γ))
          → ((x : B) → x ≈ κ′B (const x))
          → (∫ A → B)
        ∫-recursion σB _  _   _  _  (#σ a)  = σB a
        ∫-recursion σB κB κ′B p1 p2 (#κ γ)  = κB (λ (x : 𝔸) → ∫-recursion σB κB κ′B p1 p2 (γ x))
        ∫-recursion σB κB κ′B p1 p2 (#κ′ γ) = κ′B ((λ (x : 𝔸) → ∫-recursion σB κB κ′B p1 p2 (γ x)))

        postulate
          uniqueness-of-∫-recursion-1 :
             (σB : A → B) 
            → (κB : (𝔸 → B) → B)
            → (κ′B : (𝔸 → B) → B)
            → (p1B : (γ : 𝔸 → B) → ((x : 𝔸) → γ x ≈ κB γ))
            → (p2B : (x : B) → x ≈ κ′B (const x))
            → (γ : 𝔸 → ∫ A) → (x : 𝔸)
              → (∫-recursion σB κB κ′B p1B p2B) ⁎ (p1 γ x) ≈ p1B ((∫-recursion σB κB κ′B p1B p2B) ∘ γ) x

{-
      module _ (P : ∫ A → 𝒰₀) where
        ∫-induction :
          ((x : A) → (P (σ x)))
          → (κP : (γ : 𝔸 → ∫ A) → P (κ γ))
          → (κ′P : (γ : 𝔸 → ∫ A) → P (κ′ γ))   --  P(γ x) P(κ γ)
          → ((γ : 𝔸 → ∫ A) → (x : 𝔸) → transport P (p1 γ x) {!!} ≈ κP γ)
          → ((x : ∫ A) → transport P (p2 x) {!!} ≈ {!κ′P γ!})
          → ((x : ∫ A) → P x)
        ∫-induction = {!!}

-}
{-
    I-recursion : ∀ {i} {A : U i} 
              → (a₀ : A) → (a₁ : A) → (aₛ : a₀ ≈ a₁) 
              → (I → A)
    I-recursion {i} {A} a₀ a₁ aₛ #zero = a₀
    I-recursion {i} {A} a₀ a₁ aₛ #one = a₁

    I-induction : ∀ {i} {P : I → U i} (zero* : P a) (one* : P b)
             (seg* : transport P seg zero* ≈ one*) → ((i : I) →  P i)
    I-induction zero* one* seg* #zero = zero*
    I-induction zero* one* seg* #one = one*

    postulate
      uniqueness-of-I-recursion : ∀ {i} {A : U i} 
              → (a₀ : A) → (a₁ : A) → (aₛ : a₀ ≈ a₁) 
              → (I-recursion a₀ a₁ aₛ) ⁎ seg ≈ aₛ
      uniqueness-of-I-induction : ∀ {i} {P : I → U i} (zero* : P a) (one* : P b)
        (seg* : transport P seg zero* ≈ one*)
        → apd P (I-induction zero* one* seg*) seg ≈ seg*
-}
