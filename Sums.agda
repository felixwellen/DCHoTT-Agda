{-# OPTIONS --without-K #-}
{-
  Sums are defined in 'Basics.agda'.
  Here are some lemmata about sums.
-}

module Sums where
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Equivalences
  open import Contractibility


  module iterated-sums-over-independant-bases (A B : U₀) (P : A → B → U₀) where
    iterated-sum = ∑ (λ (a : A) → ∑ λ (b : B) → P a b)
    switched-iterated-sum = ∑ (λ (b : B) → ∑ λ (a : A) → P a b)

    switch : iterated-sum → switched-iterated-sum
    switch (a , (b , p)) = (b , (a , p))

    switching-is-an-equivalence : switch is-an-equivalence
    switching-is-an-equivalence =
      has-left-inverse (λ {(b , (a , p)) → (a , (b , p))}) by (λ _ → refl)
      and-right-inverse ((λ {(b , (a , p)) → (a , (b , p))})) by (λ _ → refl)

    as-sum-over-product = ∑ (λ {(a , b) → P a b})

    curry : as-sum-over-product → iterated-sum
    curry ((a , b) , p) = (a , (b , p))

    uncurry : iterated-sum → as-sum-over-product 
    uncurry (a , (b , p)) = ((a , b) , p)

    currying-is-an-equivalence : curry is-an-equivalence
    currying-is-an-equivalence =
      has-left-inverse uncurry by (λ _ → refl)
      and-right-inverse uncurry by (λ _ → refl)

  module sums-over-contractibles
    (A : U₀) (P : A → U₀) (all-contractible : (a : A) → (P a) is-contractible) where

    open _is-contractible
    
    section : A → ∑ P
    section a = (a , center (all-contractible a))

    equivalence-to-base : ∑ P ≃ A
    equivalence-to-base = ∑π₁ is-an-equivalence-because
      (has-left-inverse section
        by (λ x → (inclusion-of-the-fiber-of P over (∑π₁ x)) ⁎ ((contraction (all-contractible (∑π₁ x))) (∑π₂ x)))
       and-right-inverse section by (λ a → refl))



  module sum-of-free-path-at-a-point-is-contractible (A : U₀) (a₀ : A) where

    center : ∑ (λ (a : A) → a ≈ a₀)
    center = (a₀ , refl)

    contraction : (x : ∑ (λ (a : A) → a ≈ a₀)) → x ≈ center
    contraction (.a₀ , refl) = refl
