{-# OPTIONS --without-K #-}

module DependentTypes where 
  open import Basics 
  open import EqualityAndPaths
  open import Homotopies
  open import Fiber
  open import Equivalences
  open import HalfAdjointEquivalences
  open import Pullback
  open import PullbackSquare
  -- univalence is needed to transform pullback-squares to
  -- morphisms over U₀
  open import Univalence

  
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
  dependent-type E as-map = ∑π₁ 

  the-map-on-total-spaces-induced-by_ :
    ∀ {A′ A : U₀} {E′ : A′ → U₀} {E : A → U₀}
    → (F : morphism-of-dependent-types A′ A E′ E)
    → (∑ E′ → ∑ E)
  the-map-on-total-spaces-induced-by (over φ we-have-a-morphism-of-fibers f) = 
    λ {(a′ , e′) → ( φ(a′), (f a′)(e′) ) }

  dependent-replacement :
    ∀ {A B : U₀} (f : A → B)
    → (B → U₀)
  dependent-replacement f b = fiber-of f at b 

  fiber-transport-is-concatenation :
    ∀ {A B : U₀} (f : A → B)
    → (b b′ : B) → (γ : b ≈ b′)  
    → (a : A) (η : f(a) ≈ b) → transport (fiber-of f) γ (a is-in-the-fiber-by η) ≈ (a is-in-the-fiber-by η • γ)
  fiber-transport-is-concatenation f b .b refl a η = (λ ζ → a is-in-the-fiber-by ζ) ⁎ refl-is-right-neutral η


  -- the dependet replacement is equivalent as a map of types
  -- in the sense that the total spaces are equivalent
  -- and the triangle commutes (which is not shown because it does so definitionally)
  replacement-is-equivalent :
    ∀ {A B : U₀} (f : A → B)
    → ∑ (dependent-replacement f) ≃ A
  replacement-is-equivalent f = (λ {(b , (a is-in-the-fiber-by γ)) → a}) is-an-equivalence-because
    (has-left-inverse (λ a → f a , (a is-in-the-fiber-by refl))
      by (λ { (b , (a is-in-the-fiber-by γ))
                  →  f a , (a is-in-the-fiber-by refl)
                    ≈⟨ equality-action-on-∑ (f a) b γ (a is-in-the-fiber-by refl) ⟩
                     (b , transport (fiber-of f) γ (a is-in-the-fiber-by refl))
                    ≈⟨ (λ z → b , z) ⁎ fiber-transport-is-concatenation f (f a) b γ a refl ⟩ 
                      b , (a is-in-the-fiber-by γ) ≈∎
              })

     and-right-inverse (λ a → f a , (a is-in-the-fiber-by refl)) by (λ x → refl))

  ∑-over-One-is-trivial :
    ∀ (P : One → U₀)
    → ∑ P ≈ P(∗)
  ∑-over-One-is-trivial P = univalence
    ((λ {(∗ , p) → p }) is-an-equivalence-because
      (has-left-inverse (λ p → ∗ , p) by (λ {(∗ , p) → refl})
       and-right-inverse (λ p → ∗ , p) by (λ p → refl)))

  replacement-over-One-is-constant :
    ∀ {A : U₀} (f : A → One)
    → (dependent-replacement f) ∗ ≈ A
  replacement-over-One-is-constant f = ∑-over-One-is-trivial (dependent-replacement f) ⁻¹
                                       • univalence (replacement-is-equivalent f)

  module pullbacks-are-fiberwise-equivalences 
        {Z A B C : U₀}
        {f : A → C}  {g : B → C}
        {z₁ : Z → A} {z₂ : Z → B}
        (□ : pullback-square f g z₁ z₂) where
      
  {-

        Z -z₁→ A
        |      |
        z₂     f
        |      |
        v      v
        B -g-→ C

  -}

     left-fiber-square-at_ : (b : B) → _
     left-fiber-square-at b = fiber-square-for z₂ at b

     right-fiber-square-at_ : (b : B) → _
     right-fiber-square-at b = fiber-square-for f at (g b)

  {-
    paste in the following diagram to get an equivalence on the fibers

     Fz₂──→Z -z₁→ A←────Fg
     |⌟    |⌟     |     ⌞|
     |     z₂     f      |
     |     |      |      |
     ↓     ↓      ↓      ↓
     1 ─b─→B ─g─→ C←g(b)─1 

  -}
     second-right-square-at_ : (b : B) → _
     second-right-square-at b = pasting-of-pullback-squares (left-fiber-square-at b) □

     equivalence-at_ : (b : B) → fiber-of z₂ at b ≃ fiber-of f at (g b)
     equivalence-at b = deduce-equivalence-of-vertices (second-right-square-at b)
                          (right-fiber-square-at b)

     as-triangle-over-the-universe : dependent-replacement z₂ ⇒ dependent-replacement f ∘ g
     as-triangle-over-the-universe b = univalence (equivalence-at b)

  module fiberwise-equivalences-are-pullbacks {A′ A : U₀} {E′ : A′ → U₀} {E : A → U₀} 
      (F : morphism-of-dependent-types A′ A E′ E)
      (F-is-an-equivalence-on-fibers : F is-an-equivalence-on-all-fibers) where

      open _is-an-equivalence

      f = base-change-of F


      g : (a′ : A′) → (E′ a′ → E _)
      g a′ = F on-the-fiber-over a′
      g⁻¹ : (a′ : A′) → (E _ → E′ a′)
      g⁻¹ a′ = inverse-of (g a′) given-by (F-is-an-equivalence-on-fibers a′)

      left-invertible-at : (a′ : A′) → g⁻¹ a′ ∘ g a′ ⇒ id
      left-invertible-at a′ = unit (F-is-an-equivalence-on-fibers a′)
      right-invertible-at : (a′ : A′) → id ⇒ g a′ ∘ g⁻¹ a′
      right-invertible-at a′ =
        the-inverse-is-a-right-inverse-of g a′ by F-is-an-equivalence-on-fibers a′

      g-on-∑ : ∑ E′ → ∑ E
      g-on-∑ (a′ , e′) = (f a′ , g a′ e′)

      p′ : ∑ E′ → A′
      p′ = ∑π₁
      p : ∑ E → A
      p = ∑π₁

      f∘p′⇒p∘g-on-∑  : f ∘ p′ ⇒ p ∘ g-on-∑ 
      f∘p′⇒p∘g-on-∑ (a′ , e′) = refl

      induced-map′ : ∑ E′ → pullback p f
      induced-map′ (a′ , e′) = (f a′ , (g a′) e′) and a′ are-in-the-same-fiber-by refl

      induced-map : ∑ E′ → pullback p f
      induced-map = induced-map-to-pullback g-on-∑ ∑π₁ f∘p′⇒p∘g-on-∑

      induced-map⇒induced-map′ : induced-map ⇒ induced-map′
      induced-map⇒induced-map′ (a′ , e′) = refl
      
      induced-map⁻¹ : pullback p f → ∑ E′
      induced-map⁻¹ ((a , e) and a′ are-in-the-same-fiber-by γ) = 
        (a′ , g⁻¹ a′ (transport E γ e))

      left-invertible : induced-map⁻¹ ∘ induced-map  ⇒ id 
      left-invertible (a′ , e′) =   induced-map⁻¹ (induced-map (a′ , e′))
                                 ≈⟨ induced-map⁻¹ ⁎ induced-map⇒induced-map′ (a′ , e′) ⟩
                                    induced-map⁻¹ (induced-map′ (a′ , e′))
                                 ≈⟨ refl ⟩
                                   (a′ , g⁻¹ a′ (transport E refl (g a′ e′)))
                                 ≈⟨ refl ⟩ 
                                   (a′ , g⁻¹ a′ (id (g a′ e′)))
                                 ≈⟨ (λ (e : E′ a′) → a′ , e) ⁎ left-invertible-at a′ e′ ⟩ 
                                   (a′ , e′)
                                 ≈∎

      abstract
        right-invertible : id ⇒ induced-map ∘ induced-map⁻¹
        right-invertible ((a , e) and a′ are-in-the-same-fiber-by γ) =
                    let calculate-some-equality :  (a , e) ≈ (f a′ , g a′ (g⁻¹ a′ (transport E γ e)))
                        calculate-some-equality = (a , e)
                                                 ≈⟨ equality-action-on-∑ a (f a′) γ e ⟩
                                                  (f a′ , transport E γ e)
                                                 ≈⟨ (λ e′ → f a′ , e′) ⁎ right-invertible-at a′ (transport E γ e) ⟩
                                                  (f a′ , g a′ (g⁻¹ a′ (transport E γ e)))
                                                 ≈∎
                        calculate-p⁎-of-this-equality : p ⁎ calculate-some-equality ≈ γ
                        calculate-p⁎-of-this-equality =
                           p ⁎ ((equality-action-on-∑ a (f a′) γ e) • (((λ e′ → f a′ , e′) ⁎ right-invertible-at a′ (transport E γ e)) • refl))
                          ≈⟨ application-commutes-with-concatenation p (equality-action-on-∑ a (f a′) γ e) _ ⟩
                           p ⁎ (equality-action-on-∑ a (f a′) γ e) • p ⁎ (((λ e′ → f a′ , e′) ⁎ right-invertible-at a′ (transport E γ e)) • refl)
                          ≈⟨ (λ η → η • p ⁎ (((λ e′ → f a′ , e′) ⁎ right-invertible-at a′ (transport E γ e)) • refl)) ⁎ cancel-equality-action-on-∑-with-projection a (f a′) γ e ⟩ 
                           γ • p ⁎ (((λ e′ → f a′ , e′) ⁎ right-invertible-at a′ (transport E γ e)) • refl)
                          ≈⟨ (λ η → γ • η) ⁎
                               (λ ζ → p ⁎ ζ) ⁎
                                refl-is-right-neutral ((λ e′ → f a′ , e′) ⁎ right-invertible-at a′ (transport E γ e)) ⁻¹ ⟩ 
                           γ • p ⁎ ((λ e′ → f a′ , e′) ⁎ right-invertible-at a′ (transport E γ e))
                          ≈⟨ (λ η → γ • η) ⁎
                               cancel-orthogonal-equality-in-∑ (f a′) _ _ (right-invertible-at a′ (transport E γ e)) ⟩ 
                           γ • refl
                          ≈⟨ refl-is-right-neutral γ ⁻¹ ⟩ 
                           γ
                          ≈∎




                    in ((a , e) and a′ are-in-the-same-fiber-by γ)
                      ≈⟨ (λ η → (a , e) and a′ are-in-the-same-fiber-by η) ⁎
                            (γ
                           ≈⟨ calculate-p⁎-of-this-equality ⁻¹ ⟩
                            p ⁎ calculate-some-equality
                           ≈⟨ ⁻¹-is-selfinverse (p ⁎ calculate-some-equality) ⁻¹ ⟩
                            (p ⁎ calculate-some-equality ⁻¹) ⁻¹
                           ≈⟨ (λ η → η ⁻¹) ⁎ application-commutes-with-inversion p calculate-some-equality ⁻¹ ⟩
                            p ⁎ (calculate-some-equality ⁻¹) ⁻¹
                           ≈⟨ refl-is-right-neutral _ ⟩
                            p ⁎ (calculate-some-equality ⁻¹) ⁻¹ • refl ≈∎) ⟩ 
                       (a , e) and a′ are-in-the-same-fiber-by p ⁎ (calculate-some-equality ⁻¹) ⁻¹ • refl
                      ≈⟨ equality-action p f (f a′ , g a′ (g⁻¹ a′ (transport E γ e)))
                           (a , e) (calculate-some-equality ⁻¹) a′ refl ⁻¹ ⟩ 
                       (f a′ , (g a′) (g⁻¹ a′ (transport E γ e))) and a′ are-in-the-same-fiber-by refl
                      ≈⟨ refl ⟩
                       induced-map′ (a′ , g⁻¹ a′ (transport E γ e))
                      ≈⟨ induced-map⇒induced-map′ _ ⟩
                       induced-map (a′ , g⁻¹ a′ (transport E γ e))
                      ≈∎
      
      

      fiberwise-equivalences-are-pullbacks :
        pullback-square-with-right (dependent-type E as-map)
         bottom base-change-of F
         top the-map-on-total-spaces-induced-by F
         left (dependent-type E′ as-map)
      fiberwise-equivalences-are-pullbacks = 
        the-square-commuting-by f∘p′⇒p∘g-on-∑ 
        and-inducing-an-equivalence-by
          (has-left-inverse induced-map⁻¹ by left-invertible
           and-right-inverse induced-map⁻¹ by right-invertible)

{-
      pullbacks-are-fiberwise-equivalences :
        ∀ {Z A B C : U₀}
          {f : A → C}  {g : B → C}
          {z₁ : Z → A} {z₂ : Z → B}
        → (□ : pullback-square f g z₁ z₂)
        → 
      pullbacks-are-fiberwise-equivalences = ?
-}