{-# OPTIONS --without-K #-}

module EquivalenceCharacterization where 
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Equivalences
  open import Language
  open import Contractibility

  module contractible-fibers-characterize-equivalences {A B : U₀} (f : A → B) where
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


    to-fiber-condition :
      f is-an-equivalence → (∀ (b : B) → (fiber-of f at b) is-contractible) 
    to-fiber-condition (has-left-inverse _ by unit and-right-inverse f⁻¹ by counit) b =
      contracts-to f⁻¹ b is-in-the-fiber-by counit b ⁻¹
      by (λ {(a′ is-in-the-fiber-by γ) → {!!}})
