{-# OPTIONS --without-K #-}

module CommonEquivalences where 

  open import Basics 
  open import EqualityAndPaths
  open import Homotopies
  open import Equivalences
  open import Language


  ×-One-is-trivial : ∀ {A : U₀} → A × One ≃ A
  ×-One-is-trivial = (λ { (a , x) → a }) is-an-equivalence-because
                     (has-left-inverse (λ a → a , ∗) by (λ { (a , ∗) → refl })
                      and-right-inverse (λ a → a , ∗) by (λ a → refl))


  swap-× : ∀ {A B : U₀} → A × B → B × A
  swap-× (a , b) = (b , a)

  swap-×-is-an-equivalence :
    ∀ {A B : U₀} → swap-× {A} {B} is-an-equivalence
  swap-×-is-an-equivalence = has-left-inverse swap-× by (λ { (a , b) → refl })
                             and-right-inverse swap-× by (λ { (b , a) → refl })

  swap-×-as-equivalence : ∀ {A B : U₀} → A × B ≃ B × A
  swap-×-as-equivalence = swap-× is-an-equivalence-because swap-×-is-an-equivalence


  module proof-that-right-composition-is-an-equivalence (A : U₀) (a a′ : A) where
      -- (a -η-> a′, a′ -γ-> x)  ↦ (a -η•γ-> x)
      right-compose : ∀ {x : A} (γ : a′ ≈ x)
                      → a ≈ a′ → a ≈ x
      right-compose refl η = η
  
      go-back : ∀ {x : A} (γ : a′ ≈ x)
                → a ≈ x → a ≈ a′
      go-back refl η = η
  
      left-inverse : ∀ {x : A} (γ : a′ ≈ x) (η : a ≈ a′)
                     → go-back γ (right-compose γ η) ≈ η
      left-inverse refl η = refl
  
      right-inverse : ∀ {x : A} (γ : a′ ≈ x) (η : a ≈ x)
                     → η ≈ right-compose γ (go-back γ η)
      right-inverse refl η = refl
  
      proof : ∀ {x : A} (γ : a′ ≈ x)
              → right-compose γ is-an-equivalence
      proof γ = has-left-inverse 
                  go-back γ by left-inverse γ 
                and-right-inverse
                  go-back γ by right-inverse γ
  
  right-compose : ∀ {A : U₀} {a a′ a″ : A} (γ : a′ ≈ a″) 
                  → a ≈ a′ → a ≈ a″ 
  right-compose {_} {a} {a′} {_} γ = proof-that-right-composition-is-an-equivalence.right-compose _ a a′ γ
  
  right-compose-is-an-equivalence : ∀ {A : U₀} {a a′ a″ : A} (γ : a′ ≈ a″) 
                                    → (right-compose {_} {a} {_} {_} γ) is-an-equivalence
  right-compose-is-an-equivalence γ = proof-that-right-composition-is-an-equivalence.proof _ _ _ γ


  module ∑-is-universal (A : U₀) (P : A → U₀) where
    map-to-cone : ∀ (Z : U₀) 
                  → (∑ P → Z) → Π (λ a → (P a → Z))
    map-to-cone Z φ = λ a → λ p → φ (a , p)
  
    cone-to-map : ∀ (Z : U₀) 
                  → Π (λ a → (P a → Z)) → (∑ P → Z) 
    cone-to-map Z f (a , p) = f a p

    equivalence : ∀ (Z : U₀) 
                  → (map-to-cone Z) is-an-equivalence
    equivalence Z = has-left-inverse 
                      cone-to-map Z by (λ φ → refl) 
                    and-right-inverse 
                      cone-to-map Z by (λ f → refl)

  module proof-that-equivalences-induce-equivalences-on-path-spaces 
         (A B : U₀) (f-as-equivalence : A ≃ B) where

    f : A → B
    f = _≃_.the-equivalence f-as-equivalence
  
    left-inverse : B → A
    left-inverse = _is-an-equivalence.left-inverse (_≃_.proof-of-invertibility f-as-equivalence)
    
    f⁻¹ = left-inverse

    right-inverse : B → A
    right-inverse = _is-an-equivalence.right-inverse (_≃_.proof-of-invertibility f-as-equivalence)
    
    r = right-inverse

    unit : f⁻¹ left-inverse-of f
    unit = _is-an-equivalence.unit (_≃_.proof-of-invertibility f-as-equivalence)
  
    counit′ : right-inverse right-inverse-of f
    counit′ = _is-an-equivalence.counit (_≃_.proof-of-invertibility f-as-equivalence)

    counit : id ∼ f ∘ f⁻¹ 
    counit b = (f ⁎ (f⁻¹ ⁎ counit′ b) • f ⁎ unit (r b) • counit′ b ⁻¹) ⁻¹

    f⁎ : ∀ {a a′ : A} 
         → a ≈ a′ → f(a) ≈ f(a′)
    f⁎ γ = f ⁎ γ
  
    f⁻¹⁎ : ∀ {a a′ : A} 
         → f(a) ≈ f(a′) → a ≈ a′
    f⁻¹⁎ {a} {a′} γ = unit a ⁻¹ • f⁻¹ ⁎ γ • unit a′
  

    left-invertible : ∀ {a a′ : A} →  (γ : a ≈ a′) 
                      → f⁻¹⁎ (f⁎ γ) ≈ γ
    left-invertible {a} {.a} refl = 
                    -- n.t.s.: unit a ⁻¹ • refl • unit a′ ≈ refl
                    (λ γ → γ • unit a) ⁎ refl-is-right-neutral (unit a ⁻¹) ⁻¹ •
                      ⁻¹-is-left-inversion (unit a)

    right-invertible : ∀ {a a′ : A} (γ : f(a) ≈ f(a′))
                       → γ ≈ f⁎ (f⁻¹⁎ γ)
    right-invertible {a} {a′} γ = 
      -- from the book, proof of theorem 2.11.1
      let step1 : f⁎ (f⁻¹⁎ γ) ≈ f⁎ (f⁻¹⁎ γ) • counit (f a′) • counit (f a′) ⁻¹
          step1 = concatenating (counit (f a′)) and-its-inverse-to-the-right-of f⁎ (f⁻¹⁎ γ) changes-nothing
    
          step2 : f⁎ (f⁻¹⁎ γ) • counit (f a′) • counit (f a′) ⁻¹ 
                  ≈ counit (f a) • counit (f a) ⁻¹ • (f⁎ (f⁻¹⁎ γ) • counit (f a′) • counit (f a′) ⁻¹)
          step2 = concatenating (counit (f a)) and-its-inverse-to-the-left-of 
                      (f⁎ (f⁻¹⁎ γ) • counit (f a′) • counit (f a′) ⁻¹) 
                  changes-nothing
          naturality1 : counit (f a) ⁻¹ • f⁎ (f⁻¹⁎ γ) • counit (f a′) 
                       ≈ f⁎ (f⁻¹ ⁎ (f⁎ (f⁻¹⁎ γ)))
          naturality1 = conjugate-by-counit (f ∘ f⁻¹) counit (f⁎ (f⁻¹⁎ γ)) •
                         application-commutes-with-composition f⁻¹ f (f⁎ (f⁻¹⁎ γ)) ⁻¹
          
          apply-naturality1 : counit (f a) • counit (f a) ⁻¹ • (f⁎ (f⁻¹⁎ γ) • counit (f a′) • counit (f a′) ⁻¹)
                              ≈ counit (f a) • f⁎ (f⁻¹ ⁎ (f⁎ (f⁻¹⁎ γ))) • counit (f a′) ⁻¹
          apply-naturality1 = •-is-associative (counit (f a) • counit (f a) ⁻¹)
                                (f⁎ (f⁻¹⁎ γ) • counit (f a′)) (counit (f a′) ⁻¹)
                                •
                                (λ η → η • counit (f a′) ⁻¹) ⁎
                                •-is-associative (counit (f a)) (counit (f a) ⁻¹)
                                (f⁎ (f⁻¹⁎ γ) • counit (f a′))
                                ⁻¹
                                •
                                (λ η → counit (f a) • η • counit (f a′) ⁻¹) ⁎
                                •-is-associative (counit (f a) ⁻¹) (f⁎ (f⁻¹⁎ γ)) (counit (f a′))
                                • (λ η → counit (f a) • η • counit (f a′) ⁻¹) ⁎ naturality1

          cancel-units : f⁻¹ ⁎ (f⁎ (f⁻¹⁎ γ)) ≈ f⁻¹ ⁎ γ
          cancel-units = application-commutes-with-composition f f⁻¹ (f⁻¹⁎ γ) 
                         • (conjugate-by-unit (f⁻¹ ∘ f) unit (f⁻¹⁎ γ) ⁻¹ 
                         • ((λ η → η • unit a′ ⁻¹) ⁎
                              •-is-associative (unit a) (unit a ⁻¹ • f⁻¹ ⁎ γ) (unit a′)
                              • ((λ η → η • unit a′ • unit a′ ⁻¹) ⁎
                                   •-is-associative (unit a) (unit a ⁻¹) (f⁻¹ ⁎ γ)
                                   • •-is-associative (unit a • unit a ⁻¹ • f⁻¹ ⁎ γ) (unit a′) (unit a′ ⁻¹) ⁻¹
                                   • •-is-associative (unit a • unit a ⁻¹) (f⁻¹ ⁎ γ) (unit a′ • unit a′ ⁻¹) ⁻¹
                                   • ((cancel-the′ unit a left-of f⁻¹ ⁎ γ • (unit a′ • unit a′ ⁻¹)) 
                                   • (•-is-associative (f⁻¹ ⁎ γ) (unit a′) (unit a′ ⁻¹) 
                                   • (cancel-the′ unit a′ right-of f⁻¹ ⁎ γ)))))) 
          
          apply-cancellation : counit (f a) • f⁎ (f⁻¹ ⁎ (f⁎ (f⁻¹⁎ γ))) • counit (f a′) ⁻¹
                               ≈ counit (f a) • f⁎ (f⁻¹ ⁎ γ) • counit (f a′) ⁻¹
          apply-cancellation = (λ η → counit (f a) • f⁎ η • counit (f a′) ⁻¹) ⁎ cancel-units

          conjugate : f⁎ (f⁻¹ ⁎ γ) 
                         ≈ counit (f a) ⁻¹ • γ • counit (f a′)
          conjugate = application-commutes-with-composition f⁻¹ f γ 
                      • conjugate-by-counit (f ∘ f⁻¹) counit γ ⁻¹
  
          apply-conjugation : counit (f a) • f⁎ (f⁻¹ ⁎ γ) • counit (f a′) ⁻¹
                              ≈ γ
          apply-conjugation = (λ η → counit (f a) • η • counit (f a′) ⁻¹) ⁎ conjugate 
                              • ((λ η → η • counit (f a′) ⁻¹) ⁎
                                   •-is-associative (counit (f a)) (counit (f a) ⁻¹ • γ)
                                   (counit (f a′))
                                   • ((cancel-the′ counit (f a′) right-of
                                         counit (f a) • (counit (f a) ⁻¹ • γ))
                                        • (•-is-associative (counit (f a)) (counit (f a) ⁻¹) γ 
                                        • (cancel-the′ counit (f a) left-of γ))))
      in (step1 • step2 • apply-naturality1 • apply-cancellation • apply-conjugation) ⁻¹

    proof : ∀ {a a′ : A} → (λ (γ : a ≈ a′) → f ⁎ γ) is-an-equivalence
    proof = has-left-inverse f⁻¹⁎ by left-invertible and-right-inverse f⁻¹⁎ by right-invertible


-- algebraic manipulations of equations are equivalences
  module concatenation-is-an-equivalence 
    {A : U₀} {a a′ : A} (η ζ : a ≈ a′) where

    concatenate-right : 
                  ∀ {a″ : A} (γ : a′ ≈ a″)
                  → η ≈ ζ → η • γ ≈ ζ • γ
    concatenate-right refl H = refl-is-right-neutral η ⁻¹ • H • refl-is-right-neutral ζ

    cancel-right′ : 
                  ∀ {a″ : A} (γ : a′ ≈ a″)
                  → η • γ ≈ ζ • γ → η ≈ ζ
    cancel-right′ refl H = refl-is-right-neutral η • H • refl-is-right-neutral ζ ⁻¹

    right-invertible : 
                  ∀ {a″ : A} (γ : a′ ≈ a″)
                  → (H : η • γ ≈ ζ • γ)
                  → H ≈ concatenate-right γ (cancel-right′ γ H)
    right-invertible refl H =
      ((λ ξ → ξ • refl-is-right-neutral ζ) ⁎
         •-is-associative (refl-is-right-neutral η ⁻¹)
         (refl-is-right-neutral η • H) (refl-is-right-neutral ζ ⁻¹)
         • ((cancel-the refl-is-right-neutral ζ right-of
               refl-is-right-neutral η ⁻¹ • (refl-is-right-neutral η • H))
              • (•-is-associative (refl-is-right-neutral η ⁻¹)
                   (refl-is-right-neutral η) H
                   • (cancel-the refl-is-right-neutral η left-of H)))) ⁻¹

    left-invertible : 
                    ∀ {a″ : A} (γ : a′ ≈ a″)
                    → (H : η ≈ ζ)
                    → cancel-right′ γ (concatenate-right γ H) ≈ H
    left-invertible refl H =
      ((λ ξ → ξ • refl-is-right-neutral ζ ⁻¹) ⁎
         •-is-associative (refl-is-right-neutral η)
         (refl-is-right-neutral η ⁻¹ • H) (refl-is-right-neutral ζ)
         • ((cancel-the′ refl-is-right-neutral ζ right-of
               refl-is-right-neutral η • (refl-is-right-neutral η ⁻¹ • H))
              • (•-is-associative (refl-is-right-neutral η)
                   (refl-is-right-neutral η ⁻¹) H
                   • (cancel-the′ refl-is-right-neutral η left-of H)))) 

    proof-of-equivalence : ∀ {a″ : A} (γ : a′ ≈ a″)
                           → (concatenate-right γ) is-an-equivalence
    proof-of-equivalence γ = has-left-inverse cancel-right′ γ by left-invertible γ and-right-inverse
                               cancel-right′ γ by right-invertible γ


    cancel-right-lhs : ∀ {a″ : A} (γ : a′ ≈ a″)
                       → η • γ • γ ⁻¹ ≈ ζ → η ≈ ζ
    cancel-right-lhs refl H = refl-is-right-neutral η •
                                (λ ξ → ξ • refl) ⁎ refl-is-right-neutral η
                                • H
    decancel-right-lhs : ∀ {a″ : A} (γ : a′ ≈ a″)
                         → η ≈ ζ → η • γ • γ ⁻¹ ≈ ζ
    decancel-right-lhs refl H = ((λ ξ → ξ • refl) ⁎ refl-is-right-neutral η) ⁻¹
                                • refl-is-right-neutral η ⁻¹ 
                                  • H

    left-invertible′ : ∀ {a″ : A} (γ : a′ ≈ a″)
                      → (H : η • γ • γ ⁻¹ ≈ ζ)
                      → decancel-right-lhs γ (cancel-right-lhs γ H) ≈ H
    left-invertible′ refl H = let rη = refl-is-right-neutral η
                                  rrη = (λ ξ → ξ • refl) ⁎ rη
                              in •-is-associative (rrη ⁻¹ • rη ⁻¹) (rη • rrη) H 
                                 • (λ ξ → ξ • H) ⁎ •-is-associative (rrη ⁻¹ • rη ⁻¹) rη rrη 
                                 • (λ ξ → ξ • rrη • H) ⁎ •-is-associative (rrη ⁻¹) (rη ⁻¹) rη ⁻¹ 
                                 • (λ ξ → rrη ⁻¹ • ξ • rrη • H) ⁎ ⁻¹-is-left-inversion rη 
                                 • (λ ξ → ξ • rrη • H) ⁎ refl-is-right-neutral (rrη ⁻¹) ⁻¹ 
                                 • (cancel-the rrη left-of H)


    right-invertible′ : ∀ {a″ : A} (γ : a′ ≈ a″)
                      → (H : η ≈ ζ)
                      → H ≈ cancel-right-lhs γ (decancel-right-lhs γ H)
    right-invertible′ refl H = let rη = refl-is-right-neutral η
                                   rrη = (λ ξ → ξ • refl) ⁎ rη
                               in (•-is-associative (rη • rrη) (rrη ⁻¹ • rη ⁻¹) H 
                                   • (λ ξ → ξ • H) ⁎ •-is-associative (rη • rrη) (rrη ⁻¹) (rη ⁻¹) 
                                   • (λ ξ → ξ • rη ⁻¹ • H) ⁎ •-is-associative rη rrη ((λ ξ → ξ • refl) ⁎ rη ⁻¹) ⁻¹ 
                                   • (λ ξ → rη • ξ • rη ⁻¹ • H) ⁎ ⁻¹-is-right-inversion rrη
                                   • (λ ξ → ξ • rη ⁻¹ • H) ⁎ refl-is-right-neutral rη ⁻¹ 
                                   • (cancel-the′ rη left-of H)) ⁻¹


  concatenate-right : ∀ {A : U₀} {a a′ a″ : A} (η ζ : a ≈ a′) (γ : a′ ≈ a″)
                    → η ≈ ζ → η • γ ≈ ζ • γ
  concatenate-right η ζ γ = concatenation-is-an-equivalence.concatenate-right η ζ γ

  cancel-right′ : ∀ {A : U₀} {a a′ a″ : A} (η ζ : a ≈ a′) (γ : a′ ≈ a″)
                   → η • γ ≈ ζ • γ → η ≈ ζ 
  cancel-right′ η ζ γ = concatenation-is-an-equivalence.cancel-right′ η ζ γ

  concatenating-is-an-equivalence : 
    ∀ {A : U₀} {a a′ a″ : A} (η ζ : a ≈ a′)
    → (γ : a′ ≈ a″)
    → concatenation-is-an-equivalence.concatenate-right η ζ γ is-an-equivalence
  concatenating-is-an-equivalence η ζ γ = concatenation-is-an-equivalence.proof-of-equivalence η ζ γ

  module substitution-as-equivalence
    {A : U₀} {a a′ : A} (η : a ≈ a′) where

    substitute-right : ∀ {a″ : A} (ζ : a ≈ a′) (γ γ′ : a ≈ a′)
                     → γ ≈ γ′
                     → (γ ≈ ζ) ≃ (γ′ ≈ ζ)
    substitute-right ζ γ γ′ H = U-transport ((λ ξ → ξ ≈ ζ) ⁎ H)

    substitute-left : ∀ {a″ : A} (ζ : a″ ≈ a′) (γ γ′ : a″ ≈ a)
                     → γ ≈ γ′
                     → (γ • η ≈ ζ) ≃ (γ′ • η ≈ ζ)
    substitute-left ζ γ γ′ H = U-transport ((λ ξ → ξ • η ≈ ζ) ⁎ H)


  module inversion-is-an-equivalence
    {A : U₀} where

    proof : ∀ {a a′ : A}
            → (λ (γ : a ≈ a′) → γ ⁻¹) is-an-equivalence
    proof = has-left-inverse (λ γ → γ ⁻¹) by (λ γ → ⁻¹-is-selfinverse γ)
            and-right-inverse (λ γ → γ ⁻¹) by (λ γ → ⁻¹-is-selfinverse γ ⁻¹) 
                             

