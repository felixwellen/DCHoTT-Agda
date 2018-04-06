{-# OPTIONS --without-K #-}

module EquivalenceCharacterization where 
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Equivalences
  open import Contractibility
  open import PullbackSquare
  
  module contractible-fibers-characterize-equivalences {A B : 𝒰₀} (f : A → B) where
    open import Fiber
    open _is-contractible
    
    from-fiber-condition :
      (∀ (b : B) → (fiber-of f at b) is-contractible) → f is-an-equivalence
    from-fiber-condition proof-of-contractibility =
      let
        f⁻¹ : B → A
        f⁻¹ b = ι-fiber (center (proof-of-contractibility b))
      in has-left-inverse f⁻¹
           by (λ a → ι-fiber ⁎
                       contraction (proof-of-contractibility (f a))
                       (a is-in-the-fiber-by refl))
         and-right-inverse f⁻¹
           by (λ b → as-equality-in-the-codomain
                       (center (proof-of-contractibility b))
                       ⁻¹)


    fiber-square : (b : B) → _
    fiber-square b = fiber-square-for f at b

    square-with-equivalences :
      ∀ (a : A) (b : B) (γ : b ≈ f a)
      → f is-an-equivalence
      → pullback-square-with-right (λ (_ : 𝟙) → b)
          bottom f
          top id
          left (λ (_ : 𝟙) → a)
    square-with-equivalences a b γ f-is-an-equivalence =
      pullback-square-from-equivalence-of-maps
        (λ _ → b) (λ _ → a) id-as-equivalence (f is-an-equivalence-because f-is-an-equivalence)
        (λ a → γ)

    fibers-are-contractible :
      f is-an-equivalence
      → (b : B) → (fiber-of f at b) is-contractible
    fibers-are-contractible f-is-an-equivalence b =
      let
        f⁻¹ = right-inverse-of f given-by f-is-an-equivalence
        counit = counit-of f given-by f-is-an-equivalence
      in types-equivalent-to-contractibles-are-contractible
        (deduce-equivalence-of-vertices (rotate-cospan (fiber-square b))
         (square-with-equivalences (f⁻¹ b) b (counit b) f-is-an-equivalence))
        𝟙-is-contractible

    to-fiber-condition :
      f is-an-equivalence → (∀ (b : B) → (fiber-of f at b) is-contractible) 
    to-fiber-condition f-is-an-equivalence b = fibers-are-contractible f-is-an-equivalence b


