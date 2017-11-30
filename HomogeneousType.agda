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


  
  
  
  record _─hom→_ {A B : U₀} (A′ : homogeneous-structure-on A) (B′ : homogeneous-structure-on B) : 𝒰 where
    open homogeneous-structure-on_
    field
      φ : A → B
      φ-respects-e : φ(e A′) ≈ e B′
      φ-respects-translations : (x y : A) → ψ B′ (φ x) $≃ (φ y) ≈ φ (ψ A′ x $≃ y)
                                        -- tanking translations commutes with φ

  
  module kernel {A B : 𝒰}
    {A′ : homogeneous-structure-on A} {B′ : homogeneous-structure-on B}
    (φ′ : A′ ─hom→ B′) where

    open homogeneous-structure-on_
    open _─hom→_ φ′

    K′ : A → 𝒰
    K′ a = φ a ≈ e B′

    K : 𝒰
    K = ∑ K′

    e-K : K
    e-K = (e A′ , φ-respects-e)

{-    ψ-K′ : ∀ (x : A)
      → (a : A) → K′ a → K′ (ψ A′ x $≃ a)
    ψ-K′ x a γ = {!ψ B′ ⁎ γ!}
-}
