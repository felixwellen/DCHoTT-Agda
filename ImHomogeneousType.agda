{-# OPTIONS --without-K #-}


{-

  This module is about the homogeneous structure on ℑ(A), 
  where A is a homogeneous type.
  It turns out to be a homogeneous type again 
   -- as well as its 'kernel' 𝔻ₑ

  The arguments are basically the same as those in 'Im.agda' 
  in the section on left invertible structures on ℑ(A),
  for some left invertible A. The homogeneous types are 
  a replacement for the left invertible H-spaces.

  The name of this module is a pathetic pun.

-}

module ImHomogeneousType where
  open import Basics 
  open import EqualityAndPaths renaming (_⁻¹ to _⁻¹•)
  open import Homotopies
  open import Language
  open import Equivalences
  open import HomogeneousType
  open import Im

  module structure-on-ℑ {A : 𝒰} (A′ : homogeneous-structure-on A) where
    open homogeneous-structure-on_ A′

    ιe = ι e

    ℑψ : (x : ℑ A) → ℑ A ≃ ℑ A
    ℑψ = ℑ-induction
             (λ _ → ℑ≃-is-coreduced)
             λ (x : A) → ℑ≃ (ψ x)

    ℑψ-is-a-family-of-translations :
      (x : ℑ A) → (ℑψ x $≃ ιe) ≈ x
    ℑψ-is-a-family-of-translations =
      ℑ-induction
        (λ _ → coreduced-types-have-coreduced-identity-types _ (ℑ-is-coreduced _) _ _)
        λ a → ℑψ (ι a) $≃ ιe
             ≈⟨ (λ χ → χ $≃ ιe) ⁎  ℑ-compute-induction (λ _ → ℑ≃-is-coreduced) (λ (x : A) → ℑ≃ (ψ x)) a ⟩
              ℑ≃ (ψ a) $≃ ιe
             ≈⟨ naturality-of-ℑ-unit≃ (ψ a) e ⟩
              ι (ψ a $≃ e)
             ≈⟨ ℑ-unit ⁎ is-translation-to a ⟩
               ι a
             ≈∎

    structure : homogeneous-structure-on (ℑ A)
    structure = record { e = ιe ; ψ = ℑψ ; is-translation-to = ℑψ-is-a-family-of-translations }

