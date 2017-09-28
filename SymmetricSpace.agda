{-# OPTIONS --without-K #-}

module SymmetricSpace where 
  open import Basics 
  open import EqualityAndPaths renaming (_⁻¹ to _⁻¹•)
  open import Homotopies
  open import Language
  open import Equivalences
  open import LeftInvertibleHspace
  
  {- 
    All points of a symmetric space
    are equal up to an equivalence of the space.
    A symmetric space 'A' is pointed by 'a₀'
    and 'ψ x' is an equivalence of 'A' mapping 'a₀' to 'x'.
  -} 
  record symmetry-on_ (A : U₀) : U₀ where
    field
      a₀ : A
      ψ : (x : A) → (A ≃ A)
      is-translation-to : (x : A) → (ψ x) $≃ a₀ ≈ x


  left-invertible-H-spaces-are-symmetric :
    ∀ {A : U₀}
    → left-invertible-structure-on A → symmetry-on A
  left-invertible-H-spaces-are-symmetric
    (structure-given-by-e= e ,μ= μ ,neutral-by left-neutral and right-neutral ,left-invertible-by left-invertible)
    = record {
        a₀ = e ;
        ψ = λ x → (λ z → μ (z , x)) is-an-equivalence-because left-invertible x ;
        is-translation-to = left-neutral }
