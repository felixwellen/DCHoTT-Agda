{-# OPTIONS --without-K #-}

module Interval where
  open import Basics
  open import EqualityAndPaths

  module _ where
    private
      data #I : 𝒰₀ where
        #zero : #I
        #one : #I
    I : 𝒰₀
    I = #I

    a : I
    a = #zero

    b : I
    b = #one

    postulate
      seg : a ≈ b
    
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

