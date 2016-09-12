{-# OPTIONS --without-K #-}

module PointedTypes where 
  open import Basics
  open import EqualityAndPaths
  open import Language
  open import Integers
  open import Equivalences
  open import Pullback

  zero-map : ∀ (X Y : U₀) (y₀ : Y) 
             → (X → Y)
  zero-map _ _ y₀ = λ x → y₀


  module fiber-is-a-pullback (A B : U₀)(f : A → B)(b₀ : B) where 
    fiber-to-pullback : fiber-of f at b₀ → pullback f (b₀ as-map-from-One)
    fiber-to-pullback (x is-in-the-fiber-by γ) = x and ∗ are-in-the-same-fiber-by γ
    
    pullback-to-fiber : pullback f (b₀ as-map-from-One) → fiber-of f at b₀ 
    pullback-to-fiber (a and x are-in-the-same-fiber-by γ) = a is-in-the-fiber-by γ 

    left-invers : ∀ (x : fiber-of f at b₀)
                  → pullback-to-fiber (fiber-to-pullback x) ≈ x
    left-invers (x is-in-the-fiber-by γ) = refl

    right-invers : ∀ (x : pullback f (b₀ as-map-from-One))
                  → x ≈ fiber-to-pullback (pullback-to-fiber x) 
    right-invers (a and ∗ are-in-the-same-fiber-by γ) = refl

    proof-the-fiber-is-a-pullback : (fiber-of f at b₀) ≃ pullback f (b₀ as-map-from-One)
    proof-the-fiber-is-a-pullback =
                          the-map fiber-to-pullback
                          is-an-equivalence-because
                            (has-left-inverse pullback-to-fiber by left-invers
                             and-right-inverse pullback-to-fiber by right-invers)


  the-fiber-is-a-pullback : ∀ {A B : U₀}
                          → (f : A → B) → (b₀ : B)
                          → fiber-of f at b₀ ≃ pullback f (b₀ as-map-from-One)
  the-fiber-is-a-pullback f b₀ = fiber-is-a-pullback.proof-the-fiber-is-a-pullback _ _ f b₀
  
  point-in-fiber : {X Y : U₀} {x₀ : X} {y₀ : Y} 
             → (f : X → Y) → f(x₀) ≈ y₀ → fiber-of f at y₀ 
  point-in-fiber {X} {Y} {x₀} {y₀} f γ₀ = x₀ is-in-the-fiber-by γ₀ 

  fiber-map-is-pointed : {X Y : U₀} {x₀ : X} {y₀ : Y}
             → (f : X → Y) → (γ₀ : f(x₀) ≈ y₀) → (fiber-map f) (point-in-fiber f γ₀) ≈ x₀
  fiber-map-is-pointed f γ₀ = refl

  -- the fiber equalizes
  fiber-zeroes :  ∀ (X Y : U₀) (x₀ : X) (y₀ : Y) (f : X → Y)
                  → (γ₀ : f(x₀) ≈ y₀)
                  → (x : fiber-of f at y₀) 
                  → (f ∘ (fiber-map f))(x) ≈ (zero-map (fiber-of f at y₀ ) Y y₀)(x)
  fiber-zeroes X Y x₀ y₀ f γ₀ (x is-in-the-fiber-by γ) = γ

  -- universel property of the fiber (kind of...)
  induced-map-to-the-fiber : {X Y Z : U₀} → (f : X → Y) → (y₀ : Y) → (g : Z → X)
                             → ((z : Z) → (f(g(z)) ≈ y₀))
                             → (Z → fiber-of f y₀)
  induced-map-to-the-fiber f y₀ g H z = g z is-in-the-fiber-by H z                               

  the-induced-map-commutes : {X Y Z : U₀} → (f : X → Y) → (y₀ : Y) → (g : Z → X)
                             → (H : (z : Z) → (f(g(z)) ≈ y₀))
                             → ((z : Z) → fiber-map f (induced-map-to-the-fiber f y₀ g H z)  ≈ g(z))
  the-induced-map-commutes _ _ _ _ _ = refl                             

  -- define the long fiber sequence
  record fiber-sequence-term {X : U₀} {Y : U₀} (x₀ : X) (y₀ : Y) (f : X → Y) (γ₀ : f(x₀) ≈ y₀) : U₁ where
    constructor from_,_to_,_we-have-a-map_pointed-by_
    field
      domain : U₀
      base1 : domain
      codomain : U₀
      base2 : codomain
      map : domain → codomain
      pointedness : map(base1) ≈ base2

  fiber-sequence : (X Y : U₀) → (x₀ : X) → (y₀ : Y)
                         → (f : X → Y) → (γ₀ : f(x₀) ≈ y₀) 
                         → (n : ℕ) → fiber-sequence-term x₀ y₀ f γ₀
  fiber-sequence X Y x₀ y₀ f γ₀ zero = from X , x₀ to Y , y₀ we-have-a-map f pointed-by γ₀
  fiber-sequence X Y x₀ y₀ f γ₀ (S n) with fiber-sequence X Y x₀ y₀ f γ₀ n
  ... | from Xₙ , xₙ to Yₙ , yₙ we-have-a-map fₙ pointed-by γₙ = 
    from (fiber-of fₙ at yₙ) , (xₙ is-in-the-fiber-by γₙ) 
    to Xₙ , xₙ 
    we-have-a-map (fiber-map fₙ) 
    pointed-by (fiber-map-is-pointed fₙ γₙ)



  -- cofibers
  module _ where
    private
      data #cofiber-of {X Y : U₀} (f : X → Y) (y₀ : Y) : U₀ where
        #_in-cofiber : Y → #cofiber-of f y₀

    cofiber-of : {X Y : U₀} → (f : X → Y) → (y₀ : Y) → U₀
    cofiber-of f y₀ = #cofiber-of f y₀

    _in-cofiber : {X Y : U₀} {f : X → Y} {y₀ : Y} → Y → cofiber-of f y₀
    y in-cofiber = # y in-cofiber

    postulate
      glue : {X Y : U₀} {f : X → Y} {y₀ : Y} → (x : X) → _in-cofiber {X} {Y} {f} {y₀} (f(x)) ≈ y₀ in-cofiber

    cofiber-recursion : {X Y : U₀} (f : X → Y) (y₀ : Y)
                      → (A : U₀) → (a : Y → A) → ((x : X) → a(f(x)) ≈ a(y₀))
                      → cofiber-of f y₀ → A
    cofiber-recursion f y₀ A a H # y in-cofiber = a y

--    cofiber-induction
-- postulate uniqueness of both
    
