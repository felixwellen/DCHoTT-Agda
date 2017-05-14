{-# OPTIONS --without-K #-}

module Fiber where

  open import Basics 
  open import EqualityAndPaths
  open import Homotopies
  open import Equivalences

  data fiber-of {i j} {X : U i} {Y : U j} (f : X → Y) (y₀ : Y) : U (i ⊔ j) where
    _is-in-the-fiber-by_ : (x : X) → f(x) ≈ y₀ → fiber-of f y₀

  fiber-of_at_ : ∀ {i} {j} {X : U i} {Y : U j}
                 → (f : X → Y) → (y₀ : Y) → U (i ⊔ j)
  fiber-of f at y₀ = fiber-of f y₀
  
  fiber-map : ∀ {i} {X Y : U i} {y₀ : Y} 
            → (f : X → Y)  → fiber-of f at y₀ → X
  fiber-map f (x is-in-the-fiber-by _) = x
    
  as-point-in-the-domain : 
    ∀ {i j} {A : U i} {B : U j} {f : A → B} {b : B}
    → (fiber-of f at b) → A
  as-point-in-the-domain (a is-in-the-fiber-by _) = a

  ι-fiber = as-point-in-the-domain
  
  as-equality-in-the-codomain :
    ∀ {i} {A B : U i} {f : A → B} {b : B}
    → (x : fiber-of f at b) → f(as-point-in-the-domain x) ≈ b
  as-equality-in-the-codomain (x is-in-the-fiber-by γ) = γ
  
  equality-action-on-the-fiber-of_at_acting-on-the-point-witnessed-by_ :
    ∀ {i j} {A : U i} {B : U j} {a a′ : A} (f : A → B) (b : B) (γ : f(a) ≈ b)
    → (η : a ≈ a′) → (a is-in-the-fiber-by γ) ≈ (a′ is-in-the-fiber-by (f ⁎ η ⁻¹ • γ))
  equality-action-on-the-fiber-of_at_acting-on-the-point-witnessed-by_ f b γ refl = refl
  
  _as-map-from-One : ∀ {A : U₀} → A → (One → A)
  a as-map-from-One = λ x → a 
  
  induced-map-to-the-fiber : 
    ∀ {A B Z : U₀} (f : A → B) (b : B) 
    → (φ : Z → A) (γ : f ∘ φ ⇒ (λ _ → b))
    → (Z → fiber-of f at b)
  induced-map-to-the-fiber f b φ γ z = (φ z) is-in-the-fiber-by γ z

  fiber-as-sum :
    ∀ {A B : U₀} {f : A → B} {b : B}
    → fiber-of f at b ≃ ∑ (λ a → f(a) ≈ b)
  fiber-as-sum = (λ {(a is-in-the-fiber-by γ) → (a , γ)}) is-an-equivalence-because
                 (has-left-inverse (λ {(a , γ) → a is-in-the-fiber-by γ}) by (λ {(a is-in-the-fiber-by γ) → refl})
                  and-right-inverse (λ { (a , γ) → a is-in-the-fiber-by γ }) by (λ {(a , γ) → refl}))

  fiber-of-a-∑ :
    ∀ {i} {j} {A : U i} {P : A → U j}
    → (a : A) → fiber-of ∑π₁-from P at a ≃ P a
  fiber-of-a-∑ {_} {_} {A} {P} a =
    -- was tired when proving this, it is probably easier
    let 
      map : fiber-of ∑π₁-from P at a → P a
      map = λ {((a′ , pₐ) is-in-the-fiber-by γ) → transport P γ pₐ}
      inverse : P a → fiber-of ∑π₁-from P at a 
      inverse pₐ = (a , pₐ) is-in-the-fiber-by refl
    in map is-an-equivalence-because 
       (has-left-inverse inverse 
         by (λ {((a′ , pₐ) is-in-the-fiber-by γ) 
           →  ((a , transport P γ pₐ) is-in-the-fiber-by refl)
             ≈⟨ (equality-action-on-the-fiber-of ∑π₁-from P at a
                   acting-on-the-point-witnessed-by refl)
                  (equality-action-on-∑ a a′ (γ ⁻¹) (transport P γ pₐ)) ⟩ 
              ((a′ , transport P (γ ⁻¹) (transport P γ pₐ)) is-in-the-fiber-by 
                 (∑π₁ ⁎ equality-action-on-∑ a a′ (γ ⁻¹) (transport P γ pₐ) ⁻¹ • refl))
             ≈⟨ (λ η → (a′ , transport P (γ ⁻¹) (transport P γ pₐ)) is-in-the-fiber-by η ⁻¹ • refl) ⁎ 
                       cancel-equality-action-on-∑-with-projection a a′ (γ ⁻¹) (transport P γ pₐ)  ⟩ 
              ((a′ , transport P (γ ⁻¹) (transport P γ pₐ)) is-in-the-fiber-by ((γ ⁻¹) ⁻¹ • refl))
             ≈⟨  (λ η → (a′ , transport P (γ ⁻¹) (transport P γ pₐ)) is-in-the-fiber-by η) ⁎ 
                     (refl-is-right-neutral (γ ⁻¹ ⁻¹) ⁻¹ • ⁻¹-is-selfinverse γ) ⟩ 
              ((a′ , transport P (γ ⁻¹) (transport P γ pₐ)) is-in-the-fiber-by γ)
             ≈⟨ (equality-action-on-the-fiber-of ∑π₁-from P at a
                   acting-on-the-point-witnessed-by γ) ((inclusion-of-the-fiber-of P over a′) ⁎ 
                   transport-invertibility-backwards P γ pₐ) ⟩ 
              ((a′ , pₐ) is-in-the-fiber-by ((∑π₁-from P) ⁎ (inclusion-of-the-fiber-of P over a′) ⁎ 
                    transport-invertibility-backwards P γ pₐ ⁻¹ • γ)) 
             ≈⟨ (λ η → (a′ , pₐ) is-in-the-fiber-by η ⁻¹ • γ) ⁎ 
                cancel-orthogonal-equality-in-∑ {_} {_} {A} {P} a′ 
                  (transport P (γ ⁻¹) (transport P γ pₐ)) pₐ (transport-invertibility-backwards P γ pₐ) ⟩ 
              ((a′ , pₐ) is-in-the-fiber-by γ)
             ≈∎}) 
        and-right-inverse inverse by (λ _ → refl))

