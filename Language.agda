{-# OPTIONS --without-K #-}

module Language where 
  open import Basics
  open import EqualityAndPaths

  
  -- language constructs indicating typing
  the-map : ∀ {A B : U₀} → (A → B) → (A → B)
  the-map f = f

  This-follows-from : ∀ {A : 𝒰} → A → A
  This-follows-from = id
  
  equal-by-definition : ∀ {A : U₀} {a : A} → a ≈ a
  equal-by-definition = refl

  by-definition-of :
    ∀ {i j} {A : U i} {Z : U j} {a : A}
    → Z → a ≈ a
  by-definition-of _ = refl

  -- language constructs for readable manipulation of equations
  concatenate_on-the-right-to_ : ∀ {A : U₀} {a a′ a″ : A} {η ζ : a ≈ a′}
                                      → (γ : a′ ≈ a″)
                                      → (eq : η ≈ ζ)
                                      → η • γ ≈ ζ • γ
  concatenate γ on-the-right-to eq = (λ ξ → ξ • γ) ⁎ eq

  concatenate_on-the-left-to_ : ∀ {A : U₀} {a a′ a″ : A} {η ζ : a ≈ a′}
                                      → (γ : a″ ≈ a)
                                      → (eq : η ≈ ζ)
                                      → γ • η ≈ γ • ζ
  concatenate γ on-the-left-to eq = (λ ξ → γ • ξ) ⁎ eq


  cancel-the_left-of_ : ∀ {A : U₀} {a a′ a″ : A}
                           → (γ : a″ ≈ a)
                           → (η : a ≈ a′)
                           → γ ⁻¹ • γ • η ≈ η
  cancel-the γ left-of η = (λ ζ → ζ • η) ⁎ ⁻¹-is-left-inversion γ

  cancel-the′_left-of_ : ∀ {A : U₀} {a a′ a″ : A}
                           → (γ : a ≈ a″)
                           → (η : a ≈ a′)
                           → γ • γ ⁻¹ • η ≈ η
  cancel-the′ γ left-of η = (λ ζ → ζ • η) ⁎ ⁻¹-is-right-inversion γ

  cancel-the_right-of_ : ∀ {A : U₀} {a a′ a″ : A}
                           → (γ : a″ ≈ a′)
                           → (η : a ≈ a′)
                           → η • γ ⁻¹ • γ ≈ η
  cancel-the γ right-of η = •-is-associative η (γ ⁻¹) γ ⁻¹ •
                              (λ ζ → η • ζ) ⁎ ⁻¹-is-left-inversion γ
                              • refl-is-right-neutral η ⁻¹ 
  
  cancel-the′_right-of_ : ∀ {A : U₀} {a a′ a″ : A}
                           → (γ : a′ ≈ a″)
                           → (η : a ≈ a′)
                           → η • γ • γ ⁻¹ ≈ η
  cancel-the′ γ right-of η = •-is-associative η γ (γ ⁻¹) ⁻¹ •
                              (λ ζ → η • ζ) ⁎ ⁻¹-is-right-inversion γ
                              • refl-is-right-neutral η ⁻¹ 

  cancel_on-the-right-in_ :
    ∀ {A : U₀} {a a′ a″ : A} {η ζ : a ≈ a′}
    → (γ : a′ ≈ a″)
    → η • γ ≈ ζ • γ
    → η ≈ ζ
  cancel refl on-the-right-in H =
    refl-is-right-neutral _ • H • refl-is-right-neutral _ ⁻¹


  cancel_and_,-which-are-equal-by_,-on-the-right-in_ :
    ∀ {A : U₀} {a a′ a″ : A} {η ζ : a ≈ a′}
    → (γ : a′ ≈ a″) (γ′ : a′ ≈ a″)
    → γ ≈ γ′ 
    → η • γ ≈ ζ • γ′
    → η ≈ ζ
  cancel_and_,-which-are-equal-by_,-on-the-right-in_ {_} {_} {_} {_} {η} {ζ} γ .γ refl H =
    let
      η•γ•γ⁻¹≈ζ•γ•γ⁻¹ = concatenate (γ ⁻¹) on-the-right-to H
    in (cancel-the′ γ right-of η) ⁻¹ • η•γ•γ⁻¹≈ζ•γ•γ⁻¹ •
         (cancel-the′ γ right-of ζ)

  cancel_on-the-left-in_ :
    ∀ {A : U₀} {a a′ a″ : A} {η ζ : a′ ≈ a″}
    → (γ : a ≈ a′)
    → γ • η ≈ γ • ζ
    → η ≈ ζ
  cancel refl on-the-left-in H =
    H

  concatenating_and-its-inverse-to-the-right-of_changes-nothing :
    ∀ {A : U₀} {a a′ a″ : A} 
    → (γ : a′ ≈ a″)
    → (η : a ≈ a′)
    → η ≈ η • γ • γ ⁻¹
  concatenating γ and-its-inverse-to-the-right-of η changes-nothing =
    refl-is-right-neutral η •
      (λ ζ → η • ζ) ⁎ ⁻¹-is-right-inversion γ ⁻¹
      • •-is-associative η γ (γ ⁻¹)

  concatenating-its-inverse-and_to-the-right-of_changes-nothing :
    ∀ {A : U₀} {a a′ a″ : A} 
    → (γ : a″ ≈ a′)
    → (η : a ≈ a′)
    → η ≈ η • γ ⁻¹ • γ
  concatenating-its-inverse-and γ to-the-right-of η changes-nothing =
    refl-is-right-neutral η •
      (λ ζ → η • ζ) ⁎ ⁻¹-is-left-inversion γ ⁻¹
      • •-is-associative η (γ ⁻¹) γ

  concatenating-its-inverse-and_to-the-left-of_changes-nothing :
    ∀ {A : U₀} {a a′ a″ : A} 
    → (γ : a″ ≈ a)
    → (η : a ≈ a′)
    → η ≈ γ ⁻¹ • γ • η
  concatenating-its-inverse-and γ to-the-left-of η changes-nothing =
     refl-is-left-neutral η • (λ ζ → ζ • η) ⁎ ⁻¹-is-left-inversion γ ⁻¹

  concatenating_and-its-inverse-to-the-left-of_changes-nothing :
    ∀ {A : U₀} {a a′ a″ : A} 
    → (γ : a ≈ a″)
    → (η : a ≈ a′)
    → η ≈ γ • γ ⁻¹ • η
  concatenating γ and-its-inverse-to-the-left-of η changes-nothing =
    refl-is-left-neutral η •
      (λ ζ → ζ • η) ⁎ ⁻¹-is-right-inversion γ ⁻¹


  move-up-left : ∀ {A : U₀} {a a′ a″ : A} (γ : a ≈ a′) (γ′ : a″ ≈ a′) (γ″ : a ≈ a″)
                 → γ • γ′ ⁻¹ ≈ γ″
                 → γ ≈ γ″ • γ′
  move-up-left γ γ′ .(γ • γ′ ⁻¹) refl = 
                        refl-is-right-neutral γ 
                        • (λ η → γ • η) ⁎ ⁻¹-is-left-inversion γ′ ⁻¹ 
                        • •-is-associative γ (γ′ ⁻¹) γ′

  move-down-right : ∀ {A : U₀} {a a′ a″ : A} (γ : a ≈ a′) (γ′ : a″ ≈ a′) (γ″ : a ≈ a″)
                  → γ ≈ γ″ • γ′
                  → γ • γ′ ⁻¹ ≈ γ″
  move-down-right .(γ″ • γ′) γ′ γ″ refl = 
                       •-is-associative γ″ γ′ (γ′ ⁻¹) ⁻¹ 
                       • ((λ η → γ″ • η) ⁎ ⁻¹-is-right-inversion γ′ 
                         • refl-is-right-neutral γ″ ⁻¹)

  move-the_left-of_in-the-equation_to-the-left-hand-side :
    ∀ {A : U₀} {a a′ a″ : A} {γ : a ≈ a′} (γ″ : a ≈ a″) (γ′ : a″ ≈ a′) 
    → γ ≈ γ″ • γ′
    → γ″ ⁻¹ • γ ≈ γ′
  move-the refl left-of γ′ in-the-equation equation to-the-left-hand-side = 
    equation


  _and_ = _×_
