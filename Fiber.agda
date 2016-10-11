{-# OPTIONS --without-K #-}

module Fiber where

  open import Basics 
  open import EqualityAndPaths
  open import Homotopies

  data fiber-of {i} {X Y : U i} (f : X → Y) (y₀ : Y) : U i where
    _is-in-the-fiber-by_ : (x : X) → f(x) ≈ y₀ → fiber-of f y₀

  fiber-of_at_ : ∀ {i} {X Y : U i} 
                 → (f : X → Y) → (y₀ : Y) → U i
  fiber-of f at y₀ = fiber-of f y₀
  
  fiber-map : ∀ {i} {X Y : U i} {y₀ : Y} 
            → (f : X → Y)  → fiber-of f at y₀ → X
  fiber-map f (x is-in-the-fiber-by _) = x
    
  as-point-in-the-domain : 
    ∀ {A B : U₀} {f : A → B} {b : B}
    → (fiber-of f at b) → A
  as-point-in-the-domain (a is-in-the-fiber-by _) = a

  ι-fiber = as-point-in-the-domain
  
  as-equality-in-the-codomain :
    ∀ {A B : U₀} {f : A → B} {b : B}
    → (x : fiber-of f at b) → f(as-point-in-the-domain x) ≈ b
  as-equality-in-the-codomain (x is-in-the-fiber-by γ) = γ
  
  equality-action-on-the-fiber-of_at_acting-on-the-point-witnessed-by_ :
    ∀ {A B : U₀} {a a′ : A} (f : A → B) (b : B) (γ : f(a) ≈ b)
    → (η : a ≈ a′) → (a is-in-the-fiber-by γ) ≈ (a′ is-in-the-fiber-by (f ⁎ η ⁻¹ • γ))
  equality-action-on-the-fiber-of_at_acting-on-the-point-witnessed-by_ f b γ refl = refl
  
  _as-map-from-One : ∀ {A : U₀} → A → (One → A)
  a as-map-from-One = λ x → a 
  
  induced-map-to-the-fiber : 
    ∀ {A B Z : U₀} (f : A → B) (b : B) 
    → (φ : Z → A) (γ : f ∘ φ ⇒ (λ _ → b))
    → (Z → fiber-of f at b)
  induced-map-to-the-fiber f b φ γ z = (φ z) is-in-the-fiber-by γ z
