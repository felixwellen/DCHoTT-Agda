{-# OPTIONS --without-K #-}

module SymmetricSpace where
  open import Basics 
  open import EqualityAndPaths
  open import Homotopies
  open import Language
  open import Equivalences
  open import LeftInvertibleHspace

  {-
    Let X be pointed by x₀:X.
    Then X is symmetric, if, all points are 
    the same up to equivalence, i.e.
    for all x:X, there is an equivalence ψₓ, 
    such that ψₓ(x₀)≈x.
  -}

  record _is-symmetric (X : U₀) : U₀ where
    field
      x₀ : X
      ψ : (x : X) → (X → X)
      ψs-are-equivalences : (x : X) → ψ x is-an-equivalence
      ψ-symmetrizes : (x : X) → ((ψ x) x₀) ≈ x


  {-
    All left invertible H-spaces are examples
  -}
    
  all-left-invertible-H-spaces-are-symmetric :
    ∀ {X : U₀} → left-invertible-structure-on X → X is-symmetric
  all-left-invertible-H-spaces-are-symmetric
    (structure-given-by-e= e ,μ= μ
     ,neutral-by left-neutral and right-neutral
     ,left-invertible-by  left-invertible)
    = record { x₀ = e ;
               ψ = λ x → (λ y → μ (y , x));
               ψs-are-equivalences = λ x → left-invertible x;
               ψ-symmetrizes = λ x → left-neutral x }

  record _→s_ {X Y : U₀} (X′ : X is-symmetric) (Y′ : Y is-symmetric) : U₀ where
    open _is-symmetric
    field
      φ : X → Y
      φ-respects-structure : (x y : X) → (ψ Y′) (φ x) (φ y) ≈ φ ((ψ X′) x y)

  private
    {- shorthand for 'forgetful functor' -}
    ν = all-left-invertible-H-spaces-are-symmetric
    
  morphisms-of-left-invertible-H-spaces-are-morphisms-of-symmetric-spaces :
    ∀ {X Y : U₀} {X′ : left-invertible-structure-on X} {Y′ : left-invertible-structure-on Y}
    → (X′ →le Y′) → (ν X′) →s (ν Y′)
  morphisms-of-left-invertible-H-spaces-are-morphisms-of-symmetric-spaces
    record { f = f ; homomorphism-square = homomorphism-square }
    = record { φ = f ; φ-respects-structure = λ x y → {!homomorphism-square (x , y)!} }
