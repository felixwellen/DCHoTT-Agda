{-# OPTIONS --without-K #-}

module Contractibility where 
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Equivalences
  open import Language

  record _is-contractible {i} (A : U i) : U i where
    constructor contracts-to_by_
    field
      center : A
      contraction : (a : A) → center ≈ a

  contractible-types-are-propositions :
    ∀ {i} (A : U i)
    → A is-contractible → A is-a-proposition
  contractible-types-are-propositions A (contracts-to center by contraction) x y =
                                      contraction x ⁻¹ • contraction y

  reformulate-contractibilty-as-homotopy :
    ∀ (A : U₀) (a₀ : A)
    → id ∼ (λ a → a₀) → A is-contractible
  reformulate-contractibilty-as-homotopy A a₀ H =
    contracts-to a₀ by (λ a → H a ⁻¹)

  two-contractible-types-are-equivalent : 
    ∀ {A B : U₀} 
    → (A is-contractible) → (B is-contractible)
    → A ≃ B
  two-contractible-types-are-equivalent 
    (contracts-to a₀ by H) (contracts-to b₀ by K) =
    (λ a → b₀) is-an-equivalence-because (
      has-left-inverse (λ b → a₀) by H 
      and-right-inverse (λ b → a₀) by (λ a → reverse-homotopy K a))

  all-contractible-types-are-sets :
    ∀ (A : U₀) → A is-contractible
    → ((a a′ : A) → (γ η : a ≈ a′) → γ ≈ η)
  all-contractible-types-are-sets 
    A (contracts-to center by contraction) a a′ γ η 
    =
    let 
      compute-transport-γ = compute-path-fibration-transport center a a′ γ (contraction a)
      compute-transport-η = compute-path-fibration-transport center a a′ η (contraction a)
      lift-γ-to-path-fibration = apd (λ x → center ≈ x) contraction γ
      lift-η-to-path-fibration = apd (λ x → center ≈ x) contraction η
    in cancel (contraction a) on-the-left-in
         ( contraction a • γ 
          ≈⟨ compute-transport-γ ⁻¹ • lift-γ-to-path-fibration ⟩ 
           contraction a′
          ≈⟨ lift-η-to-path-fibration ⁻¹ • compute-transport-η ⟩ 
           contraction a • η 
          ≈∎)

  -- the following is a dead end
  -- the aim was to prove '(A → A) ≃ A' implies 'A is contractible'
  -- which is not true in general
  -- (a counterexample may be found in effective topoi)
  module cantor's-diagonal-argument {A : U₀} (φ : (A → A) ≃ A) where
    -- below, if find-distinct is a function with
    --  'find-distinct(a) ≠ a'
    -- then
    --  'cantor's-diagonal φ'
    -- is a function not in the image of φ⁻¹
    cantor's-diagonal :
      ∀ (find-distinct : A → A)
      → (A → A)
    cantor's-diagonal find-distinct a =
      find-distinct ((φ ⁻¹≃ $≃ a) a)
  
    -- we use this function constructivly to
    -- show, given an equivalence φ, that
    -- all functions f : A → A have a fixpoint
    fixpoint :
      (f : A → A) → A
    fixpoint f = φ $≃ (cantor's-diagonal f)
--    _has-a-fixpoint :
--      ∀ (f : A → A) → (fixpoint f) ≈ f (fixpoint f)
--    f has-a-fixpoint = {!!}

    a₀ = φ $≃ id
    a₁ = φ $≃ (λ a → a₀)


-- example
  One-is-contractible : One is-contractible
  One-is-contractible = contracts-to ∗ by (λ {∗ → refl})
