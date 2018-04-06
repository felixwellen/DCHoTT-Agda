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

  𝟙-is-contractible : 𝟙 is-contractible
  𝟙-is-contractible = contracts-to ∗ by (λ {∗ → refl})

  𝟙-is-contractible′ :
    ∀ {j} → (Lift {j = j} 𝟙) is-contractible
  𝟙-is-contractible′ = contracts-to (lift ∗) by (λ {(lift ∗) → refl})
  
  {- 
    from HoTT-Agda (including comment)

    Any contractible type is equivalent to (all liftings of) the unit type 
  -}
  module _ {i} {A : 𝒰 i} (h : A is-contractible) where
    open _is-contractible h
    
    lower-equiv : ∀ {i j} {A : 𝒰 i} → Lift {j = j} A ≃ A
    lower-equiv = lower is-an-equivalence-because lift is-an-inverse-by (λ _ → refl) and (λ _ → refl) 

    contractible≃𝟙 : A ≃ 𝟙
    contractible≃𝟙 =
      (λ _ → ∗) is-an-equivalence-because (λ _ → center) is-an-inverse-by
        contraction and (_is-contractible.contraction 𝟙-is-contractible)

    contractible-types-are-equivalent-to-the-lift-of-𝟙 :
      ∀ {j} → A ≃ Lift {j = j} 𝟙
    contractible-types-are-equivalent-to-the-lift-of-𝟙 =
      (lower-equiv ⁻¹≃) ∘≃ contractible≃𝟙


  types-equivalent-to-contractibles-are-contractible :
    ∀ {A B : 𝒰₀}
    → A ≃ B → B is-contractible → A is-contractible
  types-equivalent-to-contractibles-are-contractible
    (e is-an-equivalence-because (has-left-inverse e⁻¹l by unit and-right-inverse e⁻¹r by counit))
    (contracts-to center-of-B by contraction-of-B) =
      contracts-to e⁻¹l center-of-B by
        (λ a → e⁻¹l ⁎ contraction-of-B (e a) • unit a)

  reformulate-contractibilty-as-homotopy :
    ∀ (A : 𝒰₀) (a₀ : A)
    → id ∼ (λ a → a₀) → A is-contractible
  reformulate-contractibilty-as-homotopy A a₀ H =
    contracts-to a₀ by (λ a → H a ⁻¹)

  two-contractible-types-are-equivalent : 
    ∀ {A B : 𝒰₀} 
    → (A is-contractible) → (B is-contractible)
    → A ≃ B
  two-contractible-types-are-equivalent 
    (contracts-to a₀ by H) (contracts-to b₀ by K) =
    (λ a → b₀) is-an-equivalence-because (
      has-left-inverse (λ b → a₀) by H 
      and-right-inverse (λ b → a₀) by (λ a → reverse-homotopy K a))

  all-contractible-types-are-sets :
    ∀ (A : 𝒰₀) → A is-contractible
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

  maps-into-a-contractible-type-are-homotopic :
    ∀ {A B : 𝒰₀} (f g : A → B)
    → B is-contractible → f ⇒ g
  maps-into-a-contractible-type-are-homotopic f g (contracts-to center by contraction) x =
    contraction (f x) ⁻¹ • contraction (g x)

  retracts-of-contractibles-are-contractible :
    ∀ {R A : 𝒰₀} (i : R → A) (r : A → R)
    → r ∘ i ⇒ id
    → A is-contractible → R is-contractible
  retracts-of-contractibles-are-contractible i r H (contracts-to center by contraction) =
    contracts-to r center by (λ x → r ⁎ contraction (i x) • H x)
    

  J-in-terms-of-contractibility :
    ∀ {i} (A : 𝒰 i) (x₀ : A)
    → ∑ (λ (x : A) → x ≈ x₀) is-contractible
  J-in-terms-of-contractibility A x₀ = contracts-to (x₀ , refl) by (λ {(_ , refl) → refl})

  J-in-terms-of-contractibility′ :
    ∀ {i} (A : 𝒰 i) (x₀ : A)
    → ∑ (λ (x : A) → x₀ ≈ x) is-contractible
  J-in-terms-of-contractibility′ A x₀ = contracts-to (x₀ , refl) by (λ {(_ , refl) → refl})

  {-

    constant functions

  -}

  const : {X Y : 𝒰₀} → Y → (X → Y)
  const y₀ = λ _ → y₀

  constant-functions-factor-over-𝟙 :
    ∀ {X Y : 𝒰₀} (y₀ : Y)
    → const y₀ ⇒ (λ (x : 𝟙) → y₀) ∘ (λ (_ : X) → ∗) 
  constant-functions-factor-over-𝟙 y₀ = λ _ → refl

  is-constant :
    ∀ {X Y : 𝒰₀}
    → (f : X → Y)
    → 𝒰₀
  is-constant {Y = Y} f =
    ∑ λ (y : Y) → const y ⇒ f
