{-# OPTIONS --without-K #-}

module HomogeneousType where 
  open import Basics 
  open import EqualityAndPaths renaming (_⁻¹ to _⁻¹•)
  open import Homotopies
  open import Language
  open import Equivalences
  open import LeftInvertibleHspace
  
  {- 
    All points of a homogeneous space
    are equal up to an equivalence of the space.
    A homogeneous space 'A' is pointed by 'a₀'
    and 'ψ x' is an equivalence of 'A' mapping 'a₀' to 'x'.
  -} 
  record homogeneous-structure-on_ (A : U₀) : U₀ where
    field
      e : A
      ψ : (x : A) → (A ≃ A)
      is-translation-to : (x : A) → ((ψ x) $≃ e) ≈ x


  left-invertible-H-spaces-are-homogeneous :
    ∀ {A : U₀}
    → left-invertible-structure-on A → homogeneous-structure-on A
  left-invertible-H-spaces-are-homogeneous
    (structure-given-by-e= e ,μ= μ ,neutral-by left-neutral and right-neutral ,left-invertible-by left-invertible)
    = record {
        e = e ;
        ψ = λ x → (λ z → μ (z , x)) is-an-equivalence-because left-invertible x ;
        is-translation-to = left-neutral }


  
  
  
