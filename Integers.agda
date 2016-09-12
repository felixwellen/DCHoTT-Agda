{-# OPTIONS --without-K #-}

module Integers where

open import Basics public
open import EqualityAndPaths
open import Homotopies
open import Univalence

-- zero-based natural numbers
data ℕ : U₀ where
  zero : ℕ
  S : ℕ → ℕ

-- positive natural numbers
data ℕ₁ : U₀ where
  one₁ : ℕ₁
  S₁ : ℕ₁ → ℕ₁

data ℤ : U₀ where
  positive : ℕ₁ → ℤ
  zeroℤ    : ℤ
  negative : ℕ₁ → ℤ


-- successor
successor-on-ℤ : ℤ → ℤ
successor-on-ℤ (positive n)      = positive (S₁ n)
successor-on-ℤ zeroℤ             = positive one₁
successor-on-ℤ (negative one₁)   = zeroℤ
successor-on-ℤ (negative (S₁ n)) = negative n

-- predecessor 
predecessor-on-ℤ : ℤ → ℤ
predecessor-on-ℤ (positive one₁)   = zeroℤ
predecessor-on-ℤ (positive (S₁ n)) = positive n
predecessor-on-ℤ zeroℤ             = negative one₁
predecessor-on-ℤ (negative n)      = negative (S₁ n)

module counit-and-unit where
  counit : (k : ℤ) → successor-on-ℤ (predecessor-on-ℤ k) ≈ k 
  counit (negative n)      = refl
  counit zeroℤ             = refl
  counit (positive one₁)   = refl
  counit (positive (S₁ n)) = refl
  
  unit : (k : ℤ) → predecessor-on-ℤ (successor-on-ℤ k) ≈ k 
  unit (negative one₁)   = refl
  unit (negative (S₁ n)) = refl
  unit zeroℤ             = refl
  unit (positive n)      = refl

successor-as-equivalence : ℤ ≃ ℤ
successor-as-equivalence = successor-on-ℤ is-an-equivalence-because 
                          (has-left-inverse predecessor-on-ℤ by counit-and-unit.unit 
                           and-right-inverse predecessor-on-ℤ by (counit-and-unit.counit ⁻¹∼))

