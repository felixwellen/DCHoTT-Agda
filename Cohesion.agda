{-# OPTIONS --without-K #-}

module Cohesion where 
  open import Basics
  open import EqualityAndPaths
  open import Contractibility
  open import PointedTypes
  open import Univalence

  postulate
    _is-discrete : ∀ {i} → U i → U i
    discreteness-is-a-proposition : ∀ {i} → (A : U i) → (A is-discrete) is-a-proposition
    _is-codiscrete : ∀ {i} → U i → U i
    codiscreteness-is-a-proposition : ∀ {i} → (A : U i) → (A is-codiscrete) is-a-proposition

    -- # is the reflector of a reflective subuniverse
    # : ∀ {i} → U i → U i
    #-is-codiscrete : ∀ {i} → (A : U i) → (# A) is-codiscrete
    #-unit : ∀ {i} {A : U i} → A → # A
    #-universal : ∀ {i} {A B : U i}
                 → B is-codiscrete → (λ (f : # A → B) → f ∘ #-unit) is-an-equivalence
    -- dependent inverse to the above / 'induction'
    #-induction : ∀ {i} {A : U i} {B : # A → U i}
                  → (∀ (a : # A) → B(a) is-codiscrete)
                  → ((a : A) → B(#-unit a))
                  → ((a : # A) → B(a))
    #-compute-induction : ∀ {i} {A : U i} {B : # A → U i}
                        → (codiscreteness : ∀ (a : # A) → B(a) is-codiscrete)
                        → (f : (a : A) → B(#-unit a))
                        → (a : A) → (#-induction codiscreteness f) (#-unit a) ≈ f a
    #-conditions-for-lexness : ∀ {i} {A B : U i}
                             → (# A) is-contractible → (# B) is-contractible
                             → ∀ (f : A → B) (b : B) → (# (fiber-of f at b)) is-contractible

  

  #-recursion : ∀ {i} {A B : U i} 
                → B is-codiscrete 
                → (A → B) 
                → (# A → B)
  #-recursion codiscreteness f = #-induction (λ a → codiscreteness) (λ a → f a)

  #-compute-recursion : ∀ {i} {A B : U i} 
                      → (codiscreteness : B is-codiscrete)
                      → (f : A → B) 
                      → (a : A) → (#-recursion codiscreteness f) (#-unit a) ≈ f a
  #-compute-recursion codiscreteness f = #-compute-induction (λ a → codiscreteness) (λ a → f a)

  #-recursion-is-unique : ∀ {i} {A B : U i} 
                      → (codiscreteness : B is-codiscrete)
                      → (f : A → B)
                      → (f′ : # A → B) 
                      → ((a : A) → f′ (#-unit a) ≈ f a)
                      → (#a : # A) → #(f′ #a ≈ (#-recursion codiscreteness f) #a)
  #-recursion-is-unique codiscreteness f f′ H = #-induction 
                                    (λ #a → #-is-codiscrete (f′ #a ≈ #-recursion codiscreteness f #a))
                                    (λ a → #-unit (H a • #-compute-recursion codiscreteness f a ⁻¹))

  #-map : ∀ {i} {A B : U i}
          → (A → B)
          → (# A → # B)
  #-map {_} {A} {B} f = #-recursion (#-is-codiscrete B) (#-unit ∘ f)

  codiscreteness-is-equivalence-invariant : ∀ {i} {A B : U i}
                                          → A ≃ B
                                          → A is-codiscrete
                                          → B is-codiscrete
  codiscreteness-is-equivalence-invariant equivalence = transport _is-codiscrete (ua equivalence) 

  module _ where
    private 
      ##-to-# : ∀ {i} {A : U i}
                → # (# A) → # A
      ##-to-# = #-recursion (#-is-codiscrete _) id
      
      ##-to-#-∘-#-unit : ∀ {i} {A : U i}
                       → (#a : # A) → ##-to-# (#-unit #a) ≈ #a
      ##-to-#-∘-#-unit = #-compute-recursion (#-is-codiscrete _) id

      #-unit-∘-##-to-# : ∀ {i} {A : U i}
                       → (##a : # (# A)) → #-unit (##-to-# ##a) ≈ ##a
      #-unit-∘-##-to-# ##a = {!!}
      
    #-idempotent : ∀ {i} {A : U i}
                 → #-unit {i} {# A} is-an-equivalence
    #-idempotent = has-left-inverse ##-to-# by ##-to-#-∘-#-unit 
                   and-right-inverse ##-to-# by (λ ##a → #-unit-∘-##-to-# ##a ⁻¹)
  

  product-stays-codiscrete : ∀ {i} {A B : U i}
                           → A is-codiscrete → B is-codiscrete
                           → (A × B) is-codiscrete
  product-stays-codiscrete A-is-codisc B-is-codisc = {!!}
  

    -- ♭, discrete objects
--    ♭ : ∀ {i} → U i → U i
--    ♭-is-discrete : ∀ {i} → (A : U i) → (♭ A) is-discrete
--    ♭-counit : ∀ {i} {A : U i} → ♭ A → A
--    ♭-universal : ∀ {i} {A B : U i}
--                  → A is-discrete → (λ (f : A → ♭ B) → ♭-counit ∘ f) is-an-equivalence
--
--    -- dependent inverse to the above / 'induction'
--    ♭-induction : ∀ {i} {A : U i} {B : A → U i}
--                  → A is-discrete
--                  → ((a : A) → B a)
--                  → ((a : A) → ♭ (B a))
--    ♭-compute-induction : ∀ {i} {A : U i} {B : A → U i}
--                        → (discreteness : A is-discrete)
--                        → (f : (a : A) → B a)
--                        → (a : A) → ♭-counit ((♭-induction discreteness f) a) ≈ f a
--    -- possibly missing factorization related property


    -- ∫ is the reflector of a reflective subuniverse
  postulate
    ∫ :  ∀ {i} → U i → U i
    ∫-is-discrete : ∀ {i} → (A : U i) → (∫ A) is-discrete
    ∫-unit : ∀ {i} {A : U i} → A → ∫ A
--    ∫-universal : ∀ {i} {A B : U i}
--               → B is-discrete → (λ (f : ∫ A → B) → f ∘ ∫-unit) is-an-equivalence
    -- dependent inverse to the above / 'induction'
    ∫-induction : ∀ {i} {A : U i} {B : ∫ A → U i}
                  → (∀ (a : ∫ A) → B(a) is-discrete)
                  → ((a : A) → B(∫-unit a))
                  → ((a : ∫ A) → B(a))
    ∫-compute-induction : ∀ {i} {A : U i} {B : ∫ A → U i}
                        → (discreteness : ∀ (a : ∫ A) → B(a) is-discrete)
                        → (f : (a : A) → B(∫-unit a))
                        → (a : A) → (∫-induction discreteness f) (∫-unit a) ≈ f a
    -- ∫ -| ♭ -| #
--  #-distribute-× : ∀ {i} {A B : U i} 
--                   → # (A × B) → (# A) × (# B) 
--  #-distribute-× x = #-recursion {!!} {!!} {!!}

--  ♭-recursion : ∀ {i} {A B : U i}
--                → A is-discrete
--                → (A → B)
--                → (A → ♭ B)
--  ♭-recursion discreteness f = ♭-induction discreteness f
--
--  ♭-compute-recursion : ∀ {i} {A B : U i}
--                → (discreteness : A is-discrete)
--                → (f : A → B)
--                → (a : A) → ♭-counit ((♭-recursion discreteness f) a) ≈ f a
--  ♭-compute-recursion discreteness f = ♭-compute-induction discreteness f
--
--  ∫-recursion : ∀ {i} {A B : U i} 
--                → B is-discrete 
--                → (A → B) 
--                → (∫ A → B)
--  ∫-recursion discreteness f = ∫-induction (λ a → discreteness) (λ a → f a)
--
--  ∫-compute-recursion : ∀ {i} {A B : U i} 
--                      → (discreteness : B is-discrete)
--                      → (f : A → B) 
--                      → (a : A) → (∫-recursion discreteness f) (∫-unit a) ≈ f a
--  ∫-compute-recursion discreteness f = ∫-compute-induction (λ a → discreteness) (λ a → f a)

  
