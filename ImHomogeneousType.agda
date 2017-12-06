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

  The sequence indicated by the module name below is

  𝔻ₑ -→ A -→ ℑ A

  The results in this module may be summarized as follows:
  If A is homogeneous, so are 𝔻ₑ and ℑA.
  The first morphism is a homotopy fiber and the second is 
  epi iff A is formally smooth. 

  The name of this module is a pathetic pun.

-}

module ImHomogeneousType where
  open import Basics 
  open import EqualityAndPaths renaming (_⁻¹ to _⁻¹•)
  open import Homotopies
  open import Language
  open import Equivalences
  open import CommonEquivalences
  open import HomogeneousType
  open import Im
  open import FormalDisk

  module ℑ-homogene-sequence {A : 𝒰} (A′ : homogeneous-structure-on A) where
    open homogeneous-structure-on_ A′

    ιe = ι e

    ℑψ : (x : ℑ A) → ℑ A ≃ ℑ A
    ℑψ = ℑ-induction
             (λ _ → ℑ≃-is-coreduced)
             λ (x : A) → ℑ≃ (ψ x)

    ψ′ : (x : A)
       → A → A
    ψ′ x = underlying-map-of (ψ x)
        
    ℑψ′ : (x : ℑ A)
        → ℑ A → ℑ A
    ℑψ′ x = underlying-map-of (ℑψ x)

    compute-ℑψ :
      ∀ (x : A)
      → ℑψ (ι x) ≈ ℑ≃ (ψ x)
    compute-ℑψ = ℑ-compute-induction (λ _ → ℑ≃-is-coreduced) λ (x : A) → ℑ≃ (ψ x)


    ι-commutator :
      ∀ (x y : A)
      → ℑψ (ι x) $≃ (ι y)  ≈  ι (ψ x $≃ y)
    ι-commutator x y =
      let
        compute-ℑψ′ : 
          ∀ (x : A)
          → ℑψ′ (ι x) ≈ ℑ→ (ψ′ x)
        compute-ℑψ′ x = underlying-map-of ⁎ (compute-ℑψ x)
        
      in ℑψ′ (ι x) (ι y)
        ≈⟨ (λ f → f (ι y)) ⁎ compute-ℑψ′ x ⟩
         ℑ→ (ψ′ x) (ι y)
        ≈⟨ naturality-of-ℑ-unit (ψ′ x) y ⟩
         ι (ψ′ x y)
        ≈∎ 


    ℑψ-is-a-family-of-translations :
      (x : ℑ A) → (ℑψ x $≃ ιe) ≈ x
    ℑψ-is-a-family-of-translations =
      ℑ-induction
        (λ _ → coreduced-types-have-coreduced-identity-types _ (ℑ-is-coreduced _) _ _)
        (λ x → ι-commutator x e • ι ⁎ is-translation-to x)
        
    structure : homogeneous-structure-on (ℑ A)
    structure = record { e = ιe ; ψ = ℑψ ; is-translation-to = ℑψ-is-a-family-of-translations }


    𝔻ₑ′ : A → 𝒰
    𝔻ₑ′ a = e is-infinitesimally-close-to a

    𝔻ₑ = 𝔻 _ e


    module compute-translation-on-𝔻ₑ (x : A) (γ : e is-close-to x) where
      ℑ-compute-family-witness : 
        ℑψ-is-a-family-of-translations (ι x) ⁻¹• • ι-commutator x e ≈ ι ⁎ is-translation-to x ⁻¹•
      ℑ-compute-family-witness =
          ℑψ-is-a-family-of-translations (ι x) ⁻¹• • ι-commutator x e
        ≈⟨
           (λ η → η ⁻¹• • ι-commutator x e) ⁎
           ℑ-compute-induction
             (λ _ → coreduced-types-have-coreduced-identity-types _ (ℑ-is-coreduced _) _ _)
             (λ x → ι-commutator x e • ι ⁎ is-translation-to x) x
          ⟩
          (ι-commutator x e • ι ⁎ is-translation-to x) ⁻¹• • ι-commutator x e
        ≈⟨ (λ η → η • ι-commutator x e) ⁎ ⁻¹-of-product (ι-commutator x e) (ι ⁎ is-translation-to x) ⟩
          (ι ⁎ is-translation-to x ⁻¹• • ι-commutator x e ⁻¹•) • ι-commutator x e
        ≈⟨ •-is-associative (ι ⁎ is-translation-to x ⁻¹•) _ _ ⁻¹• ⟩
          ι ⁎ is-translation-to x ⁻¹• • (ι-commutator x e ⁻¹• • ι-commutator x e)
        ≈⟨ (λ η → ι ⁎ is-translation-to x ⁻¹• • η) ⁎ ⁻¹-is-left-inversion  (ι-commutator x e) ⟩
           ι ⁎ is-translation-to x ⁻¹• • refl
        ≈⟨ refl-is-right-neutral (ι ⁎ is-translation-to x ⁻¹•) ⁻¹• ⟩
          ι ⁎ is-translation-to x ⁻¹•
        ≈∎

      step1 : ∀ (a : A)
           → 𝔻ₑ′ a  ≃  ℑψ′ (ι x) (ι e) ≈ ℑψ′ (ι x) (ι a) 
      step1 a = ℑψ (ι x) ∗≃
  
      compute-step1 : step1 e $≃ refl  ≈  refl
      compute-step1 = refl


      step2 : ∀ (a : A)
           → ℑψ′ (ι x) (ι e) ≈ ℑψ′ (ι x) (ι a)
           ≃  ι x  ≈  ℑψ′ (ι x) (ι a) 
      step2 a = ℑψ-is-a-family-of-translations (ι x) ⁻¹• •l≃ 
  
      compute-step2 :
        step2 e $≃ refl  ≈  ℑψ-is-a-family-of-translations (ι x) ⁻¹•
      compute-step2 = compute-left-compose (ℑψ-is-a-family-of-translations (ι x) ⁻¹•) refl
                      • refl-is-right-neutral (ℑψ-is-a-family-of-translations (ι x) ⁻¹•) ⁻¹•
  
      step3 : ∀ (a : A)
        →  ι x  ≈  ℑψ′ (ι x) (ι a) 
        ≃  ι e  ≈  ℑψ′ (ι x) (ι a)
      step3 a = γ •l≃

      compute-step3 :
          step3 e $≃ (ℑψ-is-a-family-of-translations (ι x) ⁻¹•)
        ≈ γ • ℑψ-is-a-family-of-translations (ι x) ⁻¹•
      compute-step3 = compute-left-compose γ (ℑψ-is-a-family-of-translations (ι x) ⁻¹•)

      
      step4 : ∀ (a : A)
        →  ι e  ≈  ℑψ′ (ι x) (ι a)
        ≃  ι e  ≈ ι (ψ′ x a) 
      step4 a = (ι-commutator x a •r≃)

      compute-step4 :
        step4 e $≃ (γ • ℑψ-is-a-family-of-translations (ι x) ⁻¹•)
        ≈ γ • ι ⁎ is-translation-to x ⁻¹•
      compute-step4 =
          step4 e $≃ (γ • ℑψ-is-a-family-of-translations (ι x) ⁻¹•)
        ≈⟨ compute-right-compose ((ι-commutator x e)) _ ⟩
          (γ • ℑψ-is-a-family-of-translations (ι x) ⁻¹•) • (ι-commutator x e)
        ≈⟨ •-is-associative γ _ _ ⁻¹• ⟩
          γ • (ℑψ-is-a-family-of-translations (ι x) ⁻¹• • ι-commutator x e) 
        ≈⟨ (λ η → γ • η) ⁎  ℑ-compute-family-witness ⟩
          γ • ι ⁎ is-translation-to x ⁻¹•
        ≈∎

      ψ-𝔻ₑ′ :
         ∀ (a : A)
         → 𝔻ₑ′ a ≃ 𝔻ₑ′ (ψ′ x a)
      ψ-𝔻ₑ′ a = (step4 a) ∘≃ (step3 a) ∘≃ (step2 a) ∘≃ (step1 a)

      compute-ψ-𝔻ₑ′ :
        ψ-𝔻ₑ′ e $≃ refl ≈ γ • ι ⁎ is-translation-to x ⁻¹•
      compute-ψ-𝔻ₑ′ =
          (step4 e) ∘≃ (step3 e) ∘≃ (step2 e) $≃ refl
        ≈⟨ (λ z → (step4 e) ∘≃ (step3 e) $≃ z) ⁎ compute-step2 ⟩
          (step4 e) ∘≃ (step3 e) $≃ (ℑψ-is-a-family-of-translations (ι x) ⁻¹•)
        ≈⟨ (λ z → (step4 e) $≃ z) ⁎ compute-step3 ⟩
          (step4 e) $≃ (γ • ℑψ-is-a-family-of-translations (ι x) ⁻¹•) 
        ≈⟨ compute-step4 ⟩
           γ • ι ⁎ is-translation-to x ⁻¹•
        ≈∎




    import DependentTypes
    open DependentTypes.fiber-equivalences-along-an-equivalence-on-the-base 𝔻ₑ′ 𝔻ₑ′

    ψ-𝔻ₑ : ∀ (d : 𝔻ₑ) → 𝔻ₑ ≃ 𝔻ₑ
    ψ-𝔻ₑ (x , γ) =
      induced-map (ψ x) (compute-translation-on-𝔻ₑ.ψ-𝔻ₑ′ x γ)
      is-an-equivalence-because
      induced-map-is-an-equivalence (ψ x) (compute-translation-on-𝔻ₑ.ψ-𝔻ₑ′ x γ)

    ψ-𝔻ₑ″ : ∀ (d : 𝔻ₑ) → 𝔻ₑ → 𝔻ₑ
    ψ-𝔻ₑ″ d = underlying-map-of (ψ-𝔻ₑ d)
    
    compute-transport-in-𝔻ₑ′ : ∀ {z y : A} (η : z ≈ y) (ζ : _ ≈ _)
      →   transport (λ (a : A) → e is-close-to a) η ζ
        ≈ ζ • ι ⁎ η
    compute-transport-in-𝔻ₑ′ refl = refl-is-right-neutral

    ψ-𝔻ₑ-translates :
      ∀ (d : 𝔻ₑ)
      → ψ-𝔻ₑ d $≃ ∗-𝔻  ≈  d
    ψ-𝔻ₑ-translates (x , γ) =
        ψ-𝔻ₑ (x , γ) $≃ (e , refl)
      ≈⟨ refl ⟩
        (ψ x $≃ e , (compute-translation-on-𝔻ₑ.ψ-𝔻ₑ′ x γ e $≃ refl))
      ≈⟨ (λ z → (ψ x $≃ e , z)) ⁎ compute-translation-on-𝔻ₑ.compute-ψ-𝔻ₑ′ x γ ⟩
        (ψ x $≃ e , γ • ι ⁎ is-translation-to x ⁻¹•)
      ≈⟨  equality-action-on-∑ (ψ x $≃ e) x (is-translation-to x) (γ • ι ⁎ is-translation-to x ⁻¹•)  ⟩
        (x , transport (λ (a : A) → e is-close-to a) (is-translation-to x) (γ • ι ⁎ is-translation-to x ⁻¹•))
      ≈⟨ (λ ζ → (x , ζ)) ⁎ compute-transport-in-𝔻ₑ′ (is-translation-to x) (γ • ι ⁎ is-translation-to x ⁻¹•) ⟩
        (x , γ • ι ⁎ is-translation-to x ⁻¹• • ι ⁎ is-translation-to x)
      ≈⟨ (λ ζ → (x , ζ)) ⁎ •-is-associative γ _ _ ⁻¹• ⟩
        (x , γ • (ι ⁎ is-translation-to x ⁻¹• • ι ⁎ is-translation-to x))
      ≈⟨ (λ ζ → (x , γ • ζ)) ⁎ ⁻¹-is-left-inversion (ι ⁎ is-translation-to x ) ⟩
        (x , γ • refl)
      ≈⟨ (λ ζ → (x , ζ)) ⁎ refl-is-right-neutral γ ⁻¹• ⟩ 
        (x , γ)
      ≈∎




    homogeneous-structure : homogeneous-structure-on 𝔻ₑ
    homogeneous-structure =
      record { e = ∗-𝔻 ;
               ψ = ψ-𝔻ₑ ;
               is-translation-to = ψ-𝔻ₑ-translates } 


