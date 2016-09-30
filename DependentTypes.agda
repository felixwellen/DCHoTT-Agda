{-# OPTIONS --without-K #-}

module DependentTypes where 
  open import Basics 
  open import EqualityAndPaths
  open import Homotopies
  open import Equivalences
  open import HalfAdjointEquivalences
  open import Pullback
  open import PullbackSquare

  
  record morphism-of-dependent-types (A′ A : U₀) (E′ : A′ → U₀) (E : A → U₀) : U₀ where
    constructor over_we-have-a-morphism-of-fibers_
    field 
      base-change : A′ → A
      morphism-of-fibers : (a′ : A′) → (E′(a′) → E(base-change a′))

  base-change-of :
    ∀ {A′ A : U₀} {E′ : A′ → U₀} {E : A → U₀}
    → (F : morphism-of-dependent-types A′ A E′ E)
    → (A′ → A)
  base-change-of (over base-change we-have-a-morphism-of-fibers _) = 
    base-change

  _on-the-fiber-over_ :
    ∀ {A′ A : U₀} {E′ : A′ → U₀} {E : A → U₀}
    → (F : morphism-of-dependent-types A′ A E′ E)
    → (a′ : A′)
    → (E′(a′) → E((base-change-of F) a′))
  (over _ we-have-a-morphism-of-fibers f) on-the-fiber-over a′ = f a′

  _is-an-equivalence-on-all-fibers : 
    ∀ {A′ A : U₀} {E′ : A′ → U₀} {E : A → U₀}
    → (F : morphism-of-dependent-types A′ A E′ E)
    → U₀
  (over f we-have-a-morphism-of-fibers e) is-an-equivalence-on-all-fibers = 
    ∀ (a′ : _) → e(a′) is-an-equivalence

  dependent-type_as-map :
    ∀ {A : U₀} 
    → (E : A → U₀)
    → (∑ E → A) 
  dependent-type_as-map E = ∑π₁ 

  the-map-on-total-spaces-induced-by_ :
    ∀ {A′ A : U₀} {E′ : A′ → U₀} {E : A → U₀}
    → (F : morphism-of-dependent-types A′ A E′ E)
    → (∑ E′ → ∑ E)
  the-map-on-total-spaces-induced-by (over φ we-have-a-morphism-of-fibers f) = 
    λ {(a′ , e′) → ( φ(a′), (f a′)(e′) ) }

  module pullback-conjecture {A′ A : U₀} {E′ : A′ → U₀} {E : A → U₀} 
      (F : morphism-of-dependent-types A′ A E′ E)
      (F-is-an-equivalence-on-fibers : F is-an-equivalence-on-all-fibers) where

      f = base-change-of F

      g : (a′ : A′) → (E′ a′ → E _)
      g a′ = F on-the-fiber-over a′
      g⁻¹ : (a′ : A′) → (E _ → E′ a′)
      g⁻¹ a′ = inverse-of (g a′) given-by (F-is-an-equivalence-on-fibers a′)
      g-on-∑ : ∑ E′ → ∑ E
      g-on-∑ (a′ , e′) = (f a′ , g a′ e′)

      p′ : ∑ E′ → A′
      p′ = ∑π₁
      p : ∑ E → A
      p = ∑π₁

      f∘p′⇒p∘g-on-∑  : f ∘ p′ ⇒ p ∘ g-on-∑ 
      f∘p′⇒p∘g-on-∑ (a′ , e′) = refl

      induced-map : ∑ E′ → pullback f p
      induced-map (a′ , e′) = a′ and (f a′ , (g a′) e′) are-in-the-same-fiber-by refl

      induced-map⁻¹ : pullback f p → ∑ E′
      induced-map⁻¹ (a′ and (a , e) are-in-the-same-fiber-by γ) = 
        (a′ , g⁻¹ a′ (transport E (γ ⁻¹) e))

      

      conclusion : pullback-square-with-right (dependent-type E as-map)
        bottom base-change-of F
        top the-map-on-total-spaces-induced-by F
        left (dependent-type E′ as-map)
      conclusion = 
        commutes-by f∘p′⇒p∘g-on-∑ 
        and-the-induced-map-is-an-equivalence-by (has-left-inverse {!!} by {!!} and-right-inverse {!!} by {!!})

