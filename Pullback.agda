{-# OPTIONS --without-K #-}

module Pullback where 
  open import Basics
  open import EqualityAndPaths
  open import Equivalences
  open import HalfAdjointEquivalences
  open import Homotopies
  open import Contractibility
  open import FunctionExtensionality
  open import Language

  representability : ∀ (A : U₀) → (One → A) ≃ A
  representability A = ((λ t → t ∗) is-an-equivalence-because
                   let to-constant-map : A → (One → A)
                       to-constant-map a = λ x → a
                   in (has-left-inverse to-constant-map by (λ φ → fun-ext (λ { ∗ → refl }))
                       and-right-inverse to-constant-map by (λ (a : A) → refl)))

  record pullback {A B C : U₀} (f : A → C) (g : B → C) : U₀ where
    constructor _and_are-in-the-same-fiber-by_
    field
      a : A
      b : B 
      γ : f(a) ≈ g(b)

  p₁ : ∀ {A B C : U₀} {f : A → C} {g : B → C} → pullback f g → A
  p₁ (a and b are-in-the-same-fiber-by γ) = a
                                            
  p₂ : ∀ {A B C : U₀} {f : A → C} {g : B → C} → pullback f g → B
  p₂ (a and b are-in-the-same-fiber-by γ) = b

  p-homotopy : ∀ {A B C : U₀} {f : A → C} {g : B → C} → (x : pullback f g) → f(p₁ x) ≈ g(p₂ x)
  p-homotopy (a and b are-in-the-same-fiber-by γ) = γ

  -- because it's needed elsewhere
  p₁-of-pullback : ∀ {A B C : U₀} (f : A → C) (g : B → C) → pullback f g → A
  p₁-of-pullback f g = p₁ {_} {_} {_} {f} {g}

  p₂-of-pullback : ∀ {A B C : U₀} (f : A → C) (g : B → C) → pullback f g → B
  p₂-of-pullback f g = p₂ {_} {_} {_} {f} {g}

  p-homotopy-of-pullback : ∀ {A B C : U₀} (f : A → C) (g : B → C) → (x : pullback f g) → f(p₁ x) ≈ g(p₂ x)
  p-homotopy-of-pullback f g x = p-homotopy {_} {_} {_} {f} {g} x

  uniqueness-for-pullbacks : ∀ {A B C : U₀} {f : A → C} {g : B → C} 
                               → (x : pullback f g) →  ((p₁ x) and (p₂ x) are-in-the-same-fiber-by (p-homotopy x)) ≈ x
  uniqueness-for-pullbacks (a and b are-in-the-same-fiber-by x) = refl

  -- the path groupoid of A acts on the elements of the pullback of f and g
  equalitiy-action : ∀ {A B C : U₀} (f : A → C) (g : B → C)
                       (a a′ : A) (η : a ≈ a′) (b : B) (γ : f(a) ≈ g(b)) 
                     → in-the-type (pullback f g) we-have-an-equality
                        (a and b are-in-the-same-fiber-by γ) ≈ 
                         (a′ and b are-in-the-same-fiber-by f ⁎ η ⁻¹ • γ)
  equalitiy-action f g a .a refl b γ = refl

  -- the path groupoid of A acts on the elements of the pullback of f and g
  equalitiy-action′ : ∀ {A B C : U₀} (f : A → C) (g : B → C)
                       (b b′ : B) (η : b ≈ b′) (a : A) (γ : f(a) ≈ g(b)) 
                     → in-the-type (pullback f g) we-have-an-equality
                        (a and b are-in-the-same-fiber-by γ) ≈ 
                         (a and b′ are-in-the-same-fiber-by γ • g ⁎ η)
  equalitiy-action′ f g b .b refl a γ = (λ ξ → a and b are-in-the-same-fiber-by ξ) ⁎
                                          refl-is-right-neutral γ

  homotopy-action-as-a-map : ∀ {U V W : U₀} (u₀ : U → W) (v₀ : V → W)
                            → (T : U → U)
                            → (H : (u : U) → u ≈ T u)
                            → pullback u₀ v₀ → pullback u₀ v₀
  homotopy-action-as-a-map u₀ v₀ T H (u and v are-in-the-same-fiber-by γ) =
                          T u and v are-in-the-same-fiber-by u₀ ⁎ (H u ⁻¹) • γ



  module simple-reformulation {A B C : U₀} (f : A → C) (g : B → C) where
    fibration : A × B → U₀
    fibration (a , b) = f(a) ≈ g(b)
    as-sum : (pullback f g) ≃ ∑ fibration
    as-sum = (λ { (a and b are-in-the-same-fiber-by γ) → above (a , b) is γ }) 
             is-an-equivalence-because (
               has-left-inverse
                 (λ { (above a , b is γ) → a and b are-in-the-same-fiber-by γ })
                 by  (λ { (a and b are-in-the-same-fiber-by γ) → refl }) 
               and-right-inverse
                 (λ { (above a , b is γ) → a and b are-in-the-same-fiber-by γ })
                 by (λ { (above a , b is γ) → refl }))

    sum-of-fibers = ∑ (λ (c : C) → (fiber-of f at c) × (fiber-of g at c))
    apply-path : ∀ {c c′ : C} (a : A) (b : B) (γ : f(a) ≈ c) (η : g(b) ≈ c) → (ζ : c ≈ c′) 
               → in-the-type sum-of-fibers we-have-an-equality
                 (above c is ((a is-in-the-fiber-by γ) , (b is-in-the-fiber-by η))) 
                 ≈ (above c′ is ((a is-in-the-fiber-by γ • ζ) , (b is-in-the-fiber-by η • ζ)))
    apply-path {c} {.c} a b γ η refl =
      (λ ξ →
           above c is ((a is-in-the-fiber-by ξ) , (b is-in-the-fiber-by η)))
        ⁎ refl-is-right-neutral γ
        •
        (λ ξ →
           above c is
           ((a is-in-the-fiber-by γ • refl) , (b is-in-the-fiber-by ξ)))
        ⁎ refl-is-right-neutral η
    as-sum-of-fibers : pullback f g ≃ sum-of-fibers
    as-sum-of-fibers = (λ { (a and b are-in-the-same-fiber-by γ)
                                → above (g b) is
                                  ((a is-in-the-fiber-by γ) , (b is-in-the-fiber-by refl))
                            }) 
                       is-an-equivalence-because 
                       (has-left-inverse
                         (λ { (above c is
                                 ((a is-in-the-fiber-by γ) , (b is-in-the-fiber-by η)))
                                  → a and b are-in-the-same-fiber-by γ • η ⁻¹
                              }) 
                         by (λ { (a and b are-in-the-same-fiber-by γ) → 
                                (λ ξ → a and b are-in-the-same-fiber-by ξ) ⁎
                                refl-is-right-neutral γ ⁻¹ }) 
                        and-right-inverse 
                         (λ { (above c is
                                 ((a is-in-the-fiber-by γ) , (b is-in-the-fiber-by η)))
                                  → a and b are-in-the-same-fiber-by γ • η ⁻¹
                              }) 
                         by (λ { (above c is
                                    ((a is-in-the-fiber-by γ) , (b is-in-the-fiber-by η)))
                                     → apply-path a b γ η (η ⁻¹) 
                                     • (λ ξ →
                                            above g b is
                                            ((a is-in-the-fiber-by γ • η ⁻¹) , (b is-in-the-fiber-by ξ)))
                                         ⁎ ⁻¹-is-right-inversion η
                                 }))

  data cone {A B C : U₀} (Z : U₀) (f : A → C) (g : B → C) : U₀ where
    _and_commute-by_ : (z₁ : Z → A) → (z₂ : Z → B) → f ∘ z₁ ∼ g ∘ z₂ → cone Z f g

  pc₁ : ∀ {A B C Z : U₀} {f : A → C} {g : B → C} → cone Z f g → (Z → A)
  pc₁ (z₁ and z₂ commute-by γ) = z₁ 
  pc₂ : ∀ {A B C Z : U₀} {f : A → C} {g : B → C} → cone Z f g → (Z → B)
  pc₂ (z₁ and z₂ commute-by γ) = z₂
  pc-homotopy : ∀ {A B C Z : U₀} {f : A → C} {g : B → C} → (c : cone Z f g) → f ∘ (pc₁ c) ∼ g ∘ (pc₂ c)
  pc-homotopy (z₁ and z₂ commute-by x) z = x z

  uniqueness-for-cones : ∀ {A B C Z : U₀} → (f : A → C) → (g : B → C) 
                            → (c : cone Z f g) → ((pc₁ c) and (pc₂ c) commute-by (pc-homotopy c)) ≈ c
  uniqueness-for-cones f g (z₁ and z₂ commute-by γ) = refl

  module pullback-uniqueness where
      map-to-cone : ∀ {A B C : U₀} {f : A → C} {g : B → C} {Z : U₀} → (Z → pullback f g) → cone Z f g
      map-to-cone φ = p₁ ∘ φ and p₂ ∘ φ commute-by (λ z → p-homotopy (φ z))
                                                                          
      cone-to-map : ∀ {A B C : U₀} {f : A → C} {g : B → C} {Z : U₀} → cone Z f g → (Z → pullback f g) 
      cone-to-map (z₁ and z₂ commute-by γ) z = z₁ z and z₂ z are-in-the-same-fiber-by γ z
  
      left-invertible : ∀ {A B C : U₀} {f : A → C} {g : B → C} {Z : U₀} 
        → (φ : Z → pullback f g) → cone-to-map (map-to-cone φ) ≈ φ
      left-invertible φ = fun-ext (λ z → uniqueness-for-pullbacks (φ z))
  
      right-invertible : ∀ {A B C : U₀} {f : A → C} {g : B → C} {Z : U₀} 
        → (c : cone Z f g) →  c ≈ map-to-cone (cone-to-map c)
      right-invertible (z₁ and z₂ commute-by γ) = refl

  pullback-is-universal : ∀ {A B C : U₀} {f : A → C} {g : B → C} {Z : U₀} →  cone Z f g ≃ (Z → pullback f g)
  pullback-is-universal = 
    pullback-uniqueness.cone-to-map is-an-equivalence-because 
        (has-left-inverse pullback-uniqueness.map-to-cone by 
          (reverse-homotopy pullback-uniqueness.right-invertible)
         and-right-inverse pullback-uniqueness.map-to-cone by 
           (reverse-homotopy pullback-uniqueness.left-invertible))

  induced-map-to-pullback : 
    ∀ {Z A B C : U₀} {f : A → C} {g : B → C}
    → (z₁ : Z → A) → (z₂ : Z → B) → (γ : f ∘ z₁ ∼ g ∘ z₂)
    → (Z → pullback f g)
  induced-map-to-pullback z₁ z₂ γ z =
    (z₁ z) and (z₂ z) are-in-the-same-fiber-by γ z 

  uniqueness-of-induced-maps :
    ∀ {Z A B C : U₀} {f : A → C} {g : B → C}
    → (z₁ : Z → A) → (z₂ : Z → B) → (γ : f ∘ z₁ ∼ g ∘ z₂)
    → (φ : Z → pullback f g) → (H1 :  p₁ ∘ φ ∼ z₁) → (H2 : p₂ ∘ φ ∼ z₂)
    → ((z : Z) → f ⁎ H1 z ⁻¹ • (p-homotopy (φ z)) • g ⁎ H2 z ≈ γ z)
    → φ ∼ induced-map-to-pullback z₁ z₂ γ
  uniqueness-of-induced-maps {_} {_} {_} {_} {f} {g} 
    z₁ z₂ γ φ H1 H2 this-is-a-2-factorization z =
      φ z 
     ≈⟨ uniqueness-for-pullbacks (φ z) ⁻¹ ⟩
      (p₁ (φ z) and p₂ (φ z) are-in-the-same-fiber-by p-homotopy (φ z)) 
     ≈⟨
       equalitiy-action f g (p₁ (φ z)) (z₁ z) (H1 z) (p₂ (φ z))
       (p-homotopy (φ z))
      ⟩
      (z₁ z and p₂ (φ z) are-in-the-same-fiber-by f ⁎ H1 z ⁻¹ • p-homotopy (φ z))
     ≈⟨
          equalitiy-action′ f g (p₂ (φ z)) (z₂ z) (H2 z) (z₁ z)
          (f ⁎ H1 z ⁻¹ • p-homotopy (φ z))
      ⟩
      (z₁ z and z₂ z are-in-the-same-fiber-by f ⁎ H1 z ⁻¹ • p-homotopy (φ z) • g ⁎ H2 z)
     ≈⟨ (λ ξ → z₁ z and z₂ z are-in-the-same-fiber-by ξ) ⁎
          this-is-a-2-factorization z ⟩
      (z₁ z and z₂ z are-in-the-same-fiber-by γ z)
     ≈⟨ equal-by-definition ⟩
      induced-map-to-pullback z₁ z₂ γ z 
     ≈∎

  module products-are-special-pullbacks (A B : U₀) where
    π-A : A × B → A
    π-A = π₁

    π-B : A × B → B
    π-B = π₂

    A-to-One : A → One
    A-to-One a = ∗

    B-to-One : B → One
    B-to-One b = ∗

    induced-map : A × B → pullback A-to-One B-to-One
    induced-map = induced-map-to-pullback π-A π-B (λ x → refl)
    
    inverse : pullback A-to-One B-to-One → A × B
    inverse (a and b are-in-the-same-fiber-by γ) = (a , b)

    induced-map-is-an-equivalence : induced-map is-an-equivalence
    induced-map-is-an-equivalence = 
      has-left-inverse inverse by (λ {(a , b) → refl}) 
      and-right-inverse inverse by 
        (λ {(a and b are-in-the-same-fiber-by γ) → 
              -- n.t.s.: all γ are equal to refl_∗
              (a and b are-in-the-same-fiber-by γ)
             ≈⟨ (λ η → a and b are-in-the-same-fiber-by η) ⁎
                  all-contractible-types-are-sets One One-is-contractible ∗ ∗ γ refl ⟩
              (a and b are-in-the-same-fiber-by refl)
             ≈∎})

  -- this module was intended to take less parameters
  -- the additional parameters are due to a work around
  -- there were strange results with staight forward implementations...
  module equivalence-invariance {A A′ B C : U₀} 
      (f : A → C) (g : B → C) 
      (e : A′ → A) (proof-of-equivalence : e is-an-equivalence) where

    --   P′---------\ 
    --   |          ↓
    -- P ---→ A ←e- A′
    -- | |    |    /  
    -- ↓ ↙    ↓  ↙  f′ = f ∘ e
    -- B ---→ C


    e-as-equivalence = as-equivalence e proof-of-equivalence
    e-as-half-adjoint = equivalence-to-half-adjoint-equivalence e-as-equivalence

    e⁻¹ = inverse-of-the-half-adjoint e-as-half-adjoint
    e⁻¹∘e∼1 = left-invertibility-of-the-half-adjoint e-as-half-adjoint
    e∘e⁻¹∼1 = right-invertibility-of-the-half-adjoint e-as-half-adjoint
    half-adjointness = half-adjointness-of-the-half-adjoint e-as-half-adjoint

    f′ = f ∘ e
  
    -- we construct the obvious map between the pullbacks and 
    -- show later, that it is homotopic to the induced map
    e′ : pullback f′ g → pullback f g
    e′ (a′ and b are-in-the-same-fiber-by γ) = 
       e a′ and b are-in-the-same-fiber-by γ
  
    e′⁻¹ : pullback f g → pullback f′ g
    e′⁻¹ (a and b are-in-the-same-fiber-by γ) = 
       e⁻¹ a and b are-in-the-same-fiber-by (f ⁎ e∘e⁻¹∼1 a) • γ

    left-invertible :
      e′⁻¹ ∘ e′ ∼ id
    left-invertible
      (a′ and b are-in-the-same-fiber-by γ) =
      let
        cancel-paths = 
           f′ ⁎ e⁻¹∘e∼1 a′ ⁻¹ • (f′ ⁎ e⁻¹∘e∼1 a′ • γ) 
         ≈⟨ •-is-associative (f′ ⁎ e⁻¹∘e∼1 a′ ⁻¹) (f′ ⁎ e⁻¹∘e∼1 a′) γ ⟩ 
           f′ ⁎ e⁻¹∘e∼1 a′ ⁻¹ • f′ ⁎ e⁻¹∘e∼1 a′ • γ
         ≈⟨ ((λ ξ → ξ • γ) ⁎ ⁻¹-is-left-inversion (f′ ⁎ e⁻¹∘e∼1 a′)) ⟩
           γ
         ≈∎
                       
        switch-path-with-e = 
           f ⁎ e∘e⁻¹∼1 (e a′)
         ≈⟨ (λ ξ → f ⁎ ξ) ⁎ half-adjointness a′ ⁻¹ ⟩
           f ⁎ (e ⁎ e⁻¹∘e∼1 a′)
         ≈⟨ application-commutes-with-composition e f (e⁻¹∘e∼1 a′) ⟩ 
           f′ ⁎ e⁻¹∘e∼1 a′ 
         ≈∎

      in  (e⁻¹ (e a′) and b are-in-the-same-fiber-by (f ⁎ e∘e⁻¹∼1 (e a′)) • γ)
        ≈⟨ (λ ξ → e⁻¹ (e a′) and b are-in-the-same-fiber-by ξ • γ) ⁎ switch-path-with-e ⟩
          (e⁻¹ (e a′) and b are-in-the-same-fiber-by (f′ ⁎ e⁻¹∘e∼1 a′) • γ)
        ≈⟨ equalitiy-action f′ g (e⁻¹ (e a′)) a′ (e⁻¹∘e∼1 a′) b (f′ ⁎ e⁻¹∘e∼1 a′ • γ) ⟩
          a′ and b are-in-the-same-fiber-by f′ ⁎ e⁻¹∘e∼1 a′ ⁻¹ • (f′ ⁎ e⁻¹∘e∼1 a′ • γ)
        ≈⟨ (λ ξ → a′ and b are-in-the-same-fiber-by ξ) ⁎ cancel-paths ⟩
          (a′ and b are-in-the-same-fiber-by γ)
        ≈∎

    right-invertible :
      e′ ∘ e′⁻¹ ∼ id
    right-invertible
      (a and b are-in-the-same-fiber-by γ) =
          (e (e⁻¹ a) and b are-in-the-same-fiber-by (f ⁎ e∘e⁻¹∼1 a) • γ)
        ≈⟨  equalitiy-action f g (e (e⁻¹ a)) a (e∘e⁻¹∼1 a) b
            (f ⁎ e∘e⁻¹∼1 a • γ) ⟩
          (a and b are-in-the-same-fiber-by (f ⁎ e∘e⁻¹∼1 a ⁻¹) • ((f ⁎ e∘e⁻¹∼1 a) • γ))
        ≈⟨ (λ χ → a and b are-in-the-same-fiber-by χ) ⁎
              (•-is-associative (f ⁎ e∘e⁻¹∼1 a ⁻¹) (f ⁎ e∘e⁻¹∼1 a) γ
               • (λ ξ → ξ • γ) ⁎ ⁻¹-is-left-inversion (f ⁎ e∘e⁻¹∼1 a)) ⟩
          (a and b are-in-the-same-fiber-by γ) 
        ≈∎

    e′-is-an-equivalence : e′ is-an-equivalence
    e′-is-an-equivalence = 
      has-left-inverse e′⁻¹
        by left-invertible
      and-right-inverse e′⁻¹ 
        by right-invertible ⁻¹∼


    induced-map : pullback f′ g → pullback f g
    induced-map = induced-map-to-pullback (e ∘ p₁-of-pullback f′ g)
                    (p₂-of-pullback f′ g) (λ x → p-homotopy x)

    e′-is-the-induced-map : e′ ∼ induced-map
    e′-is-the-induced-map (a and b are-in-the-same-fiber-by γ) = refl

    the-induced-map-is-an-equivalence : induced-map is-an-equivalence
    the-induced-map-is-an-equivalence =
      equivalences-are-preserved-by-homotopy e′ induced-map
        e′-is-an-equivalence e′-is-the-induced-map

  -- invariance of pullbacks under 
  -- substitution of homotopic right-maps in the cospan
  module homotopy-invariance {A B C : U₀} 
      (f f′ : A → C) (g : B → C) (H : f′ ∼ f) where
    --   P′----\ 
    --   |     ↓
    -- P ---→ A --
    -- | |    | ⇐ |  
    -- ↓ ↙    ↓  ↙  f′ 
    -- B ---→ C

    e : pullback f′ g → pullback f g
    e (a and b are-in-the-same-fiber-by γ) = a and b are-in-the-same-fiber-by H a ⁻¹ • γ

    e⁻¹ : pullback f g → pullback f′ g
    e⁻¹ (a and b are-in-the-same-fiber-by γ) = a and b are-in-the-same-fiber-by H a • γ

    left-invertible : e⁻¹ ∘ e ∼ id
    left-invertible (a and b are-in-the-same-fiber-by γ) = 
      (λ ξ → a and b are-in-the-same-fiber-by ξ) ⁎ 
         ( H a  • (H a ⁻¹ • γ) 
          ≈⟨ •-is-associative (H a) (H a ⁻¹) γ ⟩
           H a • H a ⁻¹ • γ
          ≈⟨ (λ χ → χ • γ) ⁎ ⁻¹-is-right-inversion (H a) ⟩ 
           γ 
          ≈∎ )

    right-invertible : id ∼ e ∘ e⁻¹
    right-invertible (a and b are-in-the-same-fiber-by γ) =
      (λ ξ → a and b are-in-the-same-fiber-by ξ) ⁎
        ( H a ⁻¹ • (H a • γ) 
         ≈⟨ •-is-associative (H a ⁻¹) (H a) γ ⟩
          H a  ⁻¹ • H a • γ 
         ≈⟨ (λ χ → χ • γ) ⁎ ⁻¹-is-left-inversion (H a) ⟩
          γ 
         ≈∎) ⁻¹

    e-is-an-equivalence : e is-an-equivalence
    e-is-an-equivalence = has-left-inverse e⁻¹ by left-invertible 
                          and-right-inverse e⁻¹ by right-invertible

    e⁻¹-is-an-equivalence : e⁻¹ is-an-equivalence
    e⁻¹-is-an-equivalence = the-inverse-of e which-is-an-equivalence-by e-is-an-equivalence
                              is-again-an-equivalence

  module switching-the-maps-factors-cones-by-an-equivalence
      {A B C : U₀} (f : A → C) (g : B → C) 
      (Z : U₀) (z₁ : Z → A) (z₂ : Z → B) (γ : f ∘ z₁ ∼ g ∘ z₂) where
    e : pullback f g → pullback g f
    e = λ {(a and b are-in-the-same-fiber-by γ) → b and a are-in-the-same-fiber-by γ ⁻¹}

    e⁻¹ : pullback g f → pullback f g
    e⁻¹ = λ {(b and a are-in-the-same-fiber-by γ) → a and b are-in-the-same-fiber-by γ ⁻¹}

    e-is-an-equivalence : e is-an-equivalence 
    e-is-an-equivalence = has-left-inverse e⁻¹ 
                            by (λ { (a and b are-in-the-same-fiber-by γ) 
                                → (λ η → a and b are-in-the-same-fiber-by η) ⁎ ⁻¹-is-selfinverse γ }) 
                          and-right-inverse e⁻¹ 
                            by (λ { (a and b are-in-the-same-fiber-by γ)
                                → (λ η → a and b are-in-the-same-fiber-by η) ⁎ (⁻¹-is-selfinverse γ) ⁻¹})
    -- we show: e factors induced maps
    induced-map : Z → pullback f g
    induced-map = induced-map-to-pullback z₁ z₂ γ
    
    induced-map′ : Z → pullback g f
    induced-map′ = induced-map-to-pullback z₂ z₁ (reverse-homotopy γ)

    e-factors-induced-maps : e ∘ induced-map ∼ induced-map′
    e-factors-induced-maps z = refl
    
    -- the following is essentially the fact, that we can
    -- rotate a pullback squares around its diagonal to get 
    -- another pullback square
    -- (see the corresponding function for pullback squares)
    -- Z -i-> pullback f g
    --   \    |
    --  i′\   |e        (i = induced-map)
    --     v  v
    --  pullback g f
    -- we show, that the composition i ∘ e is an equivalence
    -- and conclude that i′ is an equivalence 
    switching-preserves-equivalences : 
      induced-map is-an-equivalence → induced-map′ is-an-equivalence
    switching-preserves-equivalences 
      induced-map-is-an-equivalence = 
      let 
        the-composition-is-an-equivalence : e ∘ induced-map is-an-equivalence
        the-composition-is-an-equivalence = 
            the-composition-of-equivalences-is-an-equivalence 
              induced-map e
              induced-map-is-an-equivalence e-is-an-equivalence
      in equivalences-are-preserved-by-homotopy 
        (e ∘ induced-map) induced-map′ 
        the-composition-is-an-equivalence 
        e-factors-induced-maps
                                                              
  -- language
  map-from_to-the-pullback-of_and_induced-by : 
    ∀ {A B C : U₀}
    → (Z : U₀)
    → (f : A → C) → (g : B → C)
    → (z₁ : Z → A) → (z₂ : Z → B) → (γ : (z : Z) → f(z₁ z) ≈ g(z₂ z))
    → (Z → pullback f g)
  map-from Z to-the-pullback-of f and g induced-by z₁ z₂ γ = 
    induced-map-to-pullback z₁ z₂ γ



  -- pullback id f
  id-pullback-to-domain : ∀ (A B : U₀) (f : A → B)
                          → pullback id f → A 
  id-pullback-to-domain A B f (b and a are-in-the-same-fiber-by γ) = a 

  domain-to-id-pullback : ∀ (A B : U₀) (f : A → B)
                           → A → pullback id f
  domain-to-id-pullback A B f a = f a and a are-in-the-same-fiber-by refl



  id-pullback-is-domain : ∀ (A B : U₀) (f : A → B)
                       → (id-pullback-to-domain A B f) is-an-equivalence
  id-pullback-is-domain A B f = has-left-inverse domain-to-id-pullback A B f
                               by (λ {(b and a are-in-the-same-fiber-by γ) →
                                         (λ η → f a and a are-in-the-same-fiber-by η) ⁎
                                         ⁻¹-is-left-inversion γ ⁻¹
                                         • (λ η → f a and a are-in-the-same-fiber-by η ⁻¹ • γ) ⁎
                                           id-has-trivial-application γ ⁻¹
                                         • equalitiy-action id f b (f a) γ a γ ⁻¹})
                             and-right-inverse domain-to-id-pullback A B f
                               by (λ x → refl)
  id-pullback-as-equivalence : ∀ (A B : U₀) (f : A → B) 
                               → pullback id f ≃ A 
  id-pullback-as-equivalence A B f = id-pullback-to-domain A B f is-an-equivalence-because
                                       id-pullback-is-domain A B f

  
      
  -- pullback f id
  id-pullback-to-domain′ : ∀ (A B : U₀) (f : A → B)
                          → pullback f id → A 
  id-pullback-to-domain′ A B f (a and b are-in-the-same-fiber-by γ) = a 

  domain-to-id-pullback′ : ∀ (A B : U₀) (f : A → B)
                           → A → pullback f id
  domain-to-id-pullback′ A B f a = a and f a are-in-the-same-fiber-by refl



  id-pullback-is-domain′ : ∀ (A B : U₀) (f : A → B)
                       → (id-pullback-to-domain′ A B f) is-an-equivalence
  id-pullback-is-domain′ A B f = has-left-inverse domain-to-id-pullback′ A B f
                               by (λ {(a and b are-in-the-same-fiber-by γ) →
                                          (a and f a are-in-the-same-fiber-by refl) 
                                         ≈⟨ (λ η → a and f a are-in-the-same-fiber-by η) ⁎
                                             ⁻¹-is-right-inversion γ ⁻¹ ⟩
                                          (a and f a are-in-the-same-fiber-by γ • γ ⁻¹) 
                                         ≈⟨ (λ η → a and f a are-in-the-same-fiber-by γ • η) ⁎
                                            id-has-trivial-application (γ ⁻¹) ⁻¹ ⟩
                                          (a and f a are-in-the-same-fiber-by γ • id ⁎ (γ ⁻¹)) 
                                         ≈⟨ equalitiy-action′ f id b (f a) (γ ⁻¹) a γ ⁻¹ ⟩
                                          (a and b are-in-the-same-fiber-by γ) 
                                         ≈∎ })
                             and-right-inverse domain-to-id-pullback′ A B f
                               by (λ x → refl)
  id-pullback-as-equivalence′ : ∀ (A B : U₀) (f : A → B) 
                               → pullback f id ≃ A 
  id-pullback-as-equivalence′ A B f = id-pullback-to-domain′ A B f is-an-equivalence-because
                                       id-pullback-is-domain′ A B f

  
      
