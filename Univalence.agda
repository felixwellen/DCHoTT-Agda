{-# OPTIONS --without-K #-}

module Univalence where 

open import Basics public
open import EqualityAndPaths public
open import Equivalences public

-- univalence
postulate 
  univalence : ∀ {i} {A B : U i} → A ≃ B → A ≈ B
  univalence-is-an-equivalence : ∀ {i} {A B : U i} → (univalence {i} {A} {B}) is-quasiinverse-of U-transport




