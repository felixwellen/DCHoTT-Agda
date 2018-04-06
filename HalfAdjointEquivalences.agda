{-# OPTIONS --without-K #-}

open import Basics
open import EqualityAndPaths
open import Homotopies
open import Equivalences
open import Language

module HalfAdjointEquivalences where

  record _is-an-half-adjoint-equivalence {A B : 𝒰₀} (f : A → B) : 𝒰₀ where
    constructor has-inverse_by_,_and-is-half-adjoint-by_
    field
      g : B → A
      left-invertible : g ∘ f ⇒ id
      right-invertible : f ∘ g ⇒ id 
      half-adjoint : (a : A) → f ⁎ left-invertible a ≈ right-invertible (f a)

  _≃ha_ : (A B : 𝒰₀) → 𝒰₀
  A ≃ha B = ∑ (λ (f : A → B) → f is-an-half-adjoint-equivalence)

  _≃ₕₐ_ = _≃ha_

  underlying-map-of-the-half-adjoint :
    ∀ {A B : 𝒰₀}
    → A ≃ha B → (A → B)
  underlying-map-of-the-half-adjoint
    (e , equivalency) = e

  inverse-of-the-half-adjoint :
    ∀ {A B : 𝒰₀}
    → A ≃ha B → (B → A)
  inverse-of-the-half-adjoint
    (_ , (has-inverse g by _ , _ and-is-half-adjoint-by _)) =
    g

  left-invertibility-of-the-half-adjoint :
    ∀ {A B : 𝒰₀}
    → (e : A ≃ha B)
    → inverse-of-the-half-adjoint e ∘ underlying-map-of-the-half-adjoint e ⇒ id 
  left-invertibility-of-the-half-adjoint
    (_ , (has-inverse _ by left-invertible , _ and-is-half-adjoint-by _)) =
    left-invertible

  right-invertibility-of-the-half-adjoint :
    ∀ {A B : 𝒰₀}
    → (e : A ≃ha B)
    → underlying-map-of-the-half-adjoint e ∘ inverse-of-the-half-adjoint e  ⇒ id 
  right-invertibility-of-the-half-adjoint
    (_ , (has-inverse _ by _ , right-invertible and-is-half-adjoint-by _)) =
    right-invertible

  half-adjointness-of-the-half-adjoint :
    ∀ {A B : 𝒰₀}
    → (e : A ≃ha B)
    → (a : A)
    → (underlying-map-of-the-half-adjoint e) ⁎ (left-invertibility-of-the-half-adjoint e) a
      ≈ (right-invertibility-of-the-half-adjoint e) (underlying-map-of-the-half-adjoint e a)
  half-adjointness-of-the-half-adjoint
    (_ , (has-inverse _ by left-invertible , right-invertible and-is-half-adjoint-by half-adjoint)) =
    half-adjoint
  

  equivalences-are-half-adjoint :
    ∀ {A B : 𝒰₀} (f : A → B)
    → f is-an-equivalence
    → f is-an-half-adjoint-equivalence
  equivalences-are-half-adjoint f 
    (has-left-inverse l by unit and-right-inverse r by counit) =
    -- use HoTT-book-thm 4.2.3
    let
      l∼r = left-and-right-inverse-are-homotopic f l r unit counit
      counit′ : f ∘ l ∼ id
      counit′ b = f ⁎ l∼r b • counit b ⁻¹
      counit′′ : f ∘ l ∼ id
      counit′′ b = counit′ (f (l b)) ⁻¹ • (f ⁎ unit (l b) • counit′ b)
      
      use-naturality : (a : _) → unit (l (f a)) ≈ (l ∘ f) ⁎ (unit a)
      use-naturality a =  unit (l (f a))
                         ≈⟨ (cancel (id ⁎ (unit a)) and (unit a)
                             ,-which-are-equal-by (id-has-trivial-application (unit a))
                             ,-on-the-right-in (naturality-of-homotopies (l ∘ f) id unit (unit a))) ⟩
                          (l ∘ f) ⁎ (unit a)
                         ≈∎
      
      apply-f : (a : _) → f ⁎ (unit (l (f a))) ≈ f ⁎ ((l ∘ f) ⁎ (unit a))
      apply-f a = (λ ξ → f ⁎ ξ) ⁎ (use-naturality a)
      
      concatenate-counit : (a : _)
        →  f ⁎ (unit (l (f a))) • counit′ (f a) ≈ f ⁎ ((l ∘ f) ⁎ (unit a)) • counit′ (f a)
      concatenate-counit a = concatenate counit′ (f a) on-the-right-to apply-f a
      
      naturality-of-counit′ : (a : _) → (f ∘ l) ⁎ (f ⁎ unit a) • counit′ (f a) ≈ counit′ (f (l (f a))) • f ⁎ unit a
      naturality-of-counit′ a =  (f ∘ l) ⁎ (f ⁎ unit a) • counit′ (f a) 
                                ≈⟨ naturality-of-homotopies (f ∘ l) id counit′ (f ⁎ unit a) ⁻¹ ⟩
                                 counit′ (f (l (f a))) • id ⁎ (f ⁎ unit a)
                                ≈⟨ (λ ξ → counit′ (f (l (f a))) • ξ) ⁎ id-has-trivial-application (f ⁎ unit a) ⟩
                                 counit′ (f (l (f a))) • f ⁎ unit a
                                ≈∎

      combine-the-last-two : (a : _) → f ⁎ (unit (l (f a))) • counit′ (f a) ≈ counit′ (f (l (f a))) • f ⁎ unit a
      combine-the-last-two a =  f ⁎ (unit (l (f a))) • counit′ (f a) 
                               ≈⟨ concatenate-counit a ⟩
                                f ⁎ ((l ∘ f) ⁎ (unit a)) • counit′ (f a)
                               ≈⟨ ( (λ ξ → ξ • counit′ (f a)) ⁎
                                      (application-commutes-with-composition (l ∘ f) f (unit a) •
                                       application-commutes-with-composition f (f ∘ l) (unit a) ⁻¹)
                                    • naturality-of-counit′ a) ⟩ 
                                counit′ (f (l (f a))) • f ⁎ unit a
                               ≈∎

    in has-inverse l by unit , counit′′
      and-is-half-adjoint-by λ a →
                           (move-the (counit′ (f (l (f a)))) left-of (f ⁎ unit a) in-the-equation
                           (combine-the-last-two a) to-the-left-hand-side) ⁻¹

  _as-half-adjoint : 
    ∀ {A B : 𝒰₀}
    → (A ≃ B)
    → A ≃ha B
  (the-equivalence is-an-equivalence-because proof-of-invertibility) as-half-adjoint = 
    (the-equivalence , 
      equivalences-are-half-adjoint the-equivalence proof-of-invertibility)

  construct-half-adjoint :
    ∀ {A B : 𝒰₀}
    → (f : A → B) → (f⁻¹ : B → A)
    → f⁻¹ ∘ f ⇒ id → f ∘ f⁻¹ ⇒ id
    → A ≃ₕₐ B
  construct-half-adjoint f f⁻¹ l r =
    (f is-an-equivalence-because
      (has-left-inverse f⁻¹ by l and-right-inverse f⁻¹ by (λ a → r a ⁻¹)))
      as-half-adjoint

  proof-that-the-equivalence_is-half-adjoint :
    ∀ {A B : 𝒰₀} 
    → (e : A ≃ B) → (underlying-map-of e) is-an-half-adjoint-equivalence
  proof-that-the-equivalence (e is-an-equivalence-because proof-of-equivalency) is-half-adjoint =
    equivalences-are-half-adjoint e proof-of-equivalency


  half-adjoint-equivalences-to-equivalences :
    ∀ {A B : 𝒰₀}
    → A ≃ha B → A ≃ B
  half-adjoint-equivalences-to-equivalences
    (e , (has-inverse e⁻¹ by unit , counit and-is-half-adjoint-by proof-of-half-adjointness)) =
    e is-an-equivalence-because (has-left-inverse e⁻¹ by unit and-right-inverse e⁻¹ by counit ⁻¹∼)

  equivalence-to-half-adjoint-equivalence :
    ∀ {A B : 𝒰₀}
    → A ≃ B → A ≃ha B
  equivalence-to-half-adjoint-equivalence e =
    ((underlying-map-of e) , proof-that-the-equivalence e is-half-adjoint)

  -- composition of half adjoint equivalences 
  infixr 70 _∘≃ha_
  _∘≃ha_ : ∀ {A B C : 𝒰₀} (g : B ≃ha C) (f : A ≃ha B) → A ≃ha C
  g ∘≃ha f = let
               to-equivalence = half-adjoint-equivalences-to-equivalences
               to-ha = equivalence-to-half-adjoint-equivalence
             in to-ha (to-equivalence g ∘≃ to-equivalence f)

  infix 60 _$≃ha
  _$≃ha :
    ∀ {A B : 𝒰₀}
    → A ≃ha B → A → B
  ψ $≃ha = (underlying-map-of-the-half-adjoint ψ)

-- inversion
  infix 80 _⁻¹≃ha
  _⁻¹≃ha : 
    ∀ {A B : 𝒰₀}
    → A ≃ha B → B ≃ha A
  f ⁻¹≃ha = equivalence-to-half-adjoint-equivalence
    (half-adjoint-equivalences-to-equivalences f ⁻¹≃)
  
  transport-as-half-adjoint :
    ∀ {A : 𝒰₀}  {x y : A}
    → (P : A → 𝒰₀) → (γ : x ≈ y) → (P x ≃ha P y)
  transport-as-half-adjoint P γ =
    equivalence-to-half-adjoint-equivalence (transport-as-equivalence P γ)
  
  {-
    switching from equivalences to half adjoints...
  -}
    
  inverse-of_given-by_ :
    ∀ {A B : 𝒰₀}
    → (f : A → B) → f is-an-equivalence
    → (B → A)
  inverse-of f given-by p =
    inverse-of-the-half-adjoint
      (equivalence-to-half-adjoint-equivalence (f is-an-equivalence-because p))

  _is-left-invertible-by_ : 
    ∀ {A B : 𝒰₀}
    → (f : A → B) → (p : f is-an-equivalence)
    → (inverse-of f given-by p) ∘ f ⇒ id
  f is-left-invertible-by p =
    left-invertibility-of-the-half-adjoint
      (equivalence-to-half-adjoint-equivalence (f is-an-equivalence-because p))
    
  _is-right-invertible-by_ :
    ∀ {A B : 𝒰₀}
    → (f : A → B) → (p : f is-an-equivalence)
    → f ∘ (inverse-of f given-by p) ⇒ id
  f is-right-invertible-by p =
    right-invertibility-of-the-half-adjoint
      (equivalence-to-half-adjoint-equivalence (f is-an-equivalence-because p))

  
