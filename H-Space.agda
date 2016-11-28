{-# OPTIONS --without-K #-}

module H-Space where 
  open import Basics 
  open import EqualityAndPaths
  open import Homotopies
  open import Language
  open import Equivalences

  record H-Space-structure-on_ (X : U₀) : U₀ where
    constructor H-Space-with-neutral-element_and-operation_left-neutral-by_and-right-neutral-by_
    field
      e : X
      μ : X × X → X
      left-neutral : ∀ (x : X) → μ (e , x) ≈ x
      right-neutral : ∀ (x : X) → μ (x , e) ≈ x

  

  module the-curried-operations-are-pointwise-equivalences
         (X : U₀) (H-Space-structure-on-X : H-Space-structure-on X) where
    open H-Space-structure-on-X
