{-# OPTIONS --without-K #-}

module HomogeneousType where 
  open import Basics 
  open import EqualityAndPaths renaming (_⁻¹ to _⁻¹•)
  open import Homotopies
  open import Language
  open import Equivalences
  open import CommonEquivalences
  open import FunctionExtensionality
  
  {- 
    All points of a homogeneous space
    are equal up to an equivalence of the space.
    A homogeneous space 'A' is pointed by 'a₀'
    and 'ψ x' is an equivalence of 'A' mapping 'a₀' to 'x'.
  -} 
  record homogeneous-structure-on_ (A : 𝒰₀) : 𝒰₀ where
    field
      e : A
      ψ : (x : A) → (A ≃ A)
      is-translation-to : (x : A) → ((ψ x) $≃ e) ≈ x

  _×ₕ_ :
    ∀ {A′ B′ : 𝒰₀}
    → homogeneous-structure-on A′ → homogeneous-structure-on B′
    → homogeneous-structure-on (A′ × B′)
  record { e = eA ; ψ = ψA ; is-translation-to = tA } ×ₕ record { e = eB ; ψ = ψB ; is-translation-to = tB }
    = record
      {
        e = (eA , eB) ;
        ψ = λ {(a , b) → ψA a ×≃ ψB b } ;
        is-translation-to = λ {(x , y) → tA x ×≈ tB y}
      }  
  
  module structure-inherited-from-codomain {A B : 𝒰₀} (B' : homogeneous-structure-on B) where

    open homogeneous-structure-on_ B'

    ψ→ : (x : A → B) →
      (A → B) ≃ (A → B)
    ψ→ x = (λ f → λ a → ψ (x a) $≃ (f a))
      is-an-equivalence-because
        (has-left-inverse (λ f → λ a → ψ (x a) ⁻¹≃l  $≃ (f a))
           by (λ f → fun-ext (λ a → unit-of-the-equivalence (ψ (x a)) (f a)))
         and-right-inverse (λ f → λ a → ψ (x a) ⁻¹≃r  $≃ (f a))
           by (λ f → fun-ext (λ a → counit-of-the-equivalence (ψ (x a)) (f a))))

    e→ : A → B
    e→ = λ _ → e

    is-translation-to→ : (x : A → B) →
      ψ→ x $≃ (e→) ≈ x
    is-translation-to→ x = fun-ext (λ a → is-translation-to (x a))

    structure : homogeneous-structure-on (A → B)
    structure = record { e = e→ ; ψ = ψ→ ; is-translation-to = is-translation-to→ }


  record _─hom→_ {A B : 𝒰₀} (A′ : homogeneous-structure-on A) (B′ : homogeneous-structure-on B) : 𝒰₀ where
    open homogeneous-structure-on_
    field
      φ : A → B
      φ-respects-e : φ(e A′) ≈ e B′
      φ-respects-translations : (x y : A) → ψ B′ (φ x) $≃ (φ y) ≈ φ (ψ A′ x $≃ y)
      all-compatible : (x : A) →
         (ψ B′ (φ x) ∗≃) $≃ φ-respects-e ⁻¹• • φ-respects-translations x (e A′) • φ ⁎ (is-translation-to A′ x) ≈ is-translation-to B′ (φ x)

      -- update: I am giving it another try....
      
      -- taking translations commutes with φ
      -- this notion of morphism is problematic, since
      -- it turned out below in the kernel construction,
      -- that the commuter should be refl on ψ (φ x) e ≈ φ (ψ x e)
      -- but enforcing this would introduce another cell, which might
      -- lead to other cells.
      -- so I stopped here and tried to do what I want to know directly
      -- for the one known example of a morphism, i.e. the unit ι of ℑ
  
  module kernel {A B : 𝒰₀}
    {A′ : homogeneous-structure-on A} {B′ : homogeneous-structure-on B}
    (φ′ : A′ ─hom→ B′) where

    open homogeneous-structure-on_
    open _─hom→_ φ′

    K′ : A → 𝒰₀
    K′ a = φ a ≈ e B′

    K : 𝒰₀
    K = ∑ λ a → φ a ≈ e B′

    e-K : K
    e-K = (e A′ , φ-respects-e)

    ψ-K′ : ∀ (p : K)
      → (a : A) → K′ a ≃ K′ (ψ A′ (∑π₁ p) $≃ a)
    ψ-K′ (x , γ) a =
      let
        ψ-φ⟨x⟩ = ψ B′ (φ x)
        ψ-φ⟨x⟩′ = underlying-map-of ψ-φ⟨x⟩
        
      in  (K′ a)
        ≃⟨ equivalent-by-definition ⟩
          (φ a  ≈  e B′)
        ≃⟨ ψ-φ⟨x⟩ ∗≃ ⟩ 
          (ψ-φ⟨x⟩′ (φ a)  ≈  ψ-φ⟨x⟩′ (e B′))
        ≃⟨ is-translation-to B′ (φ x) •r≃ ⟩ 
          (ψ-φ⟨x⟩′ (φ a)  ≈  φ(x))
        ≃⟨ γ •r≃ ⟩ 
          (ψ-φ⟨x⟩′ (φ a)  ≈  e B′)
        ≃⟨ (φ-respects-translations x a •l≃) ⁻¹≃ ⟩
          (φ (ψ A′ x $≃ a)  ≈  e B′)
        ≃⟨ equivalent-by-definition ⟩
        
          K′ (ψ A′ x $≃ a)
        ≃∎

    import DependentTypes
    open DependentTypes.fiber-equivalences-along-an-equivalence-on-the-base K′ K′

    ψ-K : ∀ (p : K) → K ≃ K
    ψ-K (x , γ) =
      induced-map (ψ A′ x) (ψ-K′ (x , γ))
      is-an-equivalence-because
      induced-map-is-an-equivalence (ψ A′ x) (ψ-K′ (x , γ))

{- discontinued - reasons are at the morphism definition
    𝒯 :
      ∀ (x : A)
      → K′ (ψ A′ x $≃ e A′) ≃ K′ x
    𝒯 x = transport-as-equivalence K′ (is-translation-to A′ x)
    -- K′ e   ≃   φ e ≈ e B′  ≃   K′ x
    the-ψ-K′-translate :
      ∀ (p : K)
      → (𝒯 (∑π₁ p) ∘≃ ψ-K′ p (e A′)) $≃ φ-respects-e  ≈  ∑π₂ p
    the-ψ-K′-translate (x , γ) =
    
       (𝒯 x ∘≃ ψ-K′ (x , γ) (e A′)) $≃ φ-respects-e
       
      ≈⟨ {!!} ⟩
      
       γ
       
      ≈∎

    homogeneous-structure : homogeneous-structure-on K
    homogeneous-structure =
      record { e = e-K ;
               ψ = ψ-K ;
               is-translation-to = {!!} } 
--
-}
