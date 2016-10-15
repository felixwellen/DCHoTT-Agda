{-# OPTIONS --without-K #-}

module Univalence where 

  open import Basics public
  open import EqualityAndPaths public
  open import Equivalences public

  -- univalence
  postulate 
    univalence : ∀ {i} {A B : U i} → A ≃ B → A ≈ B
    univalence-is-an-equivalence : ∀ {i} {A B : U i} → (univalence {i} {A} {B}) is-quasiinverse-of U-transport

  propositions-are-equivalence-invariant :
    ∀ {P : U₀ → U₀} {A A′ : U₀}
    → (A ≃ A′) → P A → P A′
  propositions-are-equivalence-invariant e = transport _ (univalence e)

  the-proposition_is-equivalence-invariant-by-univalence_ :
    ∀ {i} (P : U i → U i) {A A′ : U i}
    → (A ≃ A′) → P A → P A′
  the-proposition P is-equivalence-invariant-by-univalence e = transport _ (univalence e)


