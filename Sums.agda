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


  the-map-of-sums-given-by_is-an-equivalence-since-it-is-fiberwise-an-equivalence-by_ :
    ∀ {A : U₀} {P Q : A → U₀}
    → (e : (a : A) → ((P a) → (Q a))) → ((a : A) → (e a) is-an-equivalence)
    → (λ {(a , pₐ) → (a , ((e a) pₐ))}) is-an-equivalence
  the-map-of-sums-given-by_is-an-equivalence-since-it-is-fiberwise-an-equivalence-by_ {A} {P} {Q} e e-is-an-equivalence
    =
    let
      open _is-an-equivalence
      e⁻¹l : (a : A) → (Q a → P a)
      e⁻¹l = λ a → left-inverse (e-is-an-equivalence a)
      e⁻¹r : (a : A) → (Q a → P a)
      e⁻¹r = λ a → right-inverse (e-is-an-equivalence a)
      unit : (a : A) → (e⁻¹l a) ∘ e a ⇒ id 
      unit = λ a → unit (e-is-an-equivalence a)
      counit : (a : A) → id ⇒ e a ∘ (e⁻¹r a) 
      counit = λ a → counit (e-is-an-equivalence a)
    in has-left-inverse (λ {(a , qₐ) → (a , (e⁻¹l a) qₐ)})
          by (λ {(a , pₐ) → construct-path-in-∑ a a _ _ refl (unit a pₐ)})
       and-right-inverse (λ {(a , qₐ) → (a , (e⁻¹r a) qₐ)})
          by (λ {(a , qₐ) → construct-path-in-∑ a a _ _ refl (counit a qₐ)})


  the-equivalence-of-sums-given-by_being-fiberwise-an-equivalence-by_ :
    ∀ {A : U₀} {P Q : A → U₀}
    → (e : (a : A) → ((P a) → (Q a))) → ((a : A) → (e a) is-an-equivalence)
    → ∑ P ≃ ∑ Q
  the-equivalence-of-sums-given-by e being-fiberwise-an-equivalence-by e-is-an-equivalence =
     (λ {(a , pₐ) → (a , (e a) pₐ)}) is-an-equivalence-because
      (the-map-of-sums-given-by e is-an-equivalence-since-it-is-fiberwise-an-equivalence-by e-is-an-equivalence)
    
  module iterated-sums-over-independent-bases (A B : U₀) (P : A → B → U₀) where
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

    uncurrying-is-an-equivalence : uncurry is-an-equivalence
    uncurrying-is-an-equivalence =
      has-left-inverse curry by (λ _ → refl)
      and-right-inverse curry by (λ _ → refl)

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

    open _≃_

    section-is-an-equivalence : section is-an-equivalence
    section-is-an-equivalence =
      the-inverse-of ∑π₁ which-is-an-equivalence-by
      (proof-of-invertibility equivalence-to-base) is-again-an-equivalence 

  module sum-of-free-path-at-a-point-is-contractible (A : U₀) (a₀ : A) where

    center : ∑ (λ (a : A) → a ≈ a₀)
    center = (a₀ , refl)

    contraction : (x : ∑ (λ (a : A) → a ≈ a₀)) → x ≈ center
    contraction (_ , refl) = refl

