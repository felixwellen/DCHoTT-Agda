{-# OPTIONS --without-K #-}

module NonAssociativeGroup where 
  open import Basics 
  open import EqualityAndPaths
  open import Homotopies
  open import Language
  open import Equivalences
  open import InfinityGroups

  record non-associative-group-structure-on_ (X : U₀) : U₀ where
    constructor
      non-associative-group-with-neutral-element_and-operation_left-neutral-by_,-right-neutral-by_,-left-invertible-by_and-right-invertible-by_
    field
      e : X
      μ : X × X → X
      left-neutral : ∀ (x : X) → μ (e , x) ≈ x
      right-neutral : ∀ (x : X) → μ (x , e) ≈ x
      -- the following means, that for all a,b in X, there is an contractbile space
      -- of x'es such that: xa=b
      -- therefore, 'invertible' should may also be u 'cancellable'
      left-invertible : ∀ (x₀ : X) → (λ x → μ (x , x₀)) is-an-equivalence
      right-invertible : ∀ (x₀ : X) → (λ x → μ (x₀ , x)) is-an-equivalence


--  construct-inversion-map :
--    ∀ ()

  module opposite-group {X : U₀} (group-structure-on-X : non-associative-group-structure-on X) where
    open non-associative-group-structure-on_ group-structure-on-X

    e′ = e
    
    μ′ : X × X → X
    μ′ (x , x′) = μ (x′ , x)

    structure : non-associative-group-structure-on X
    structure = record {
                       e = e;
                       μ = μ′;
                       left-neutral = right-neutral;
                       right-neutral = left-neutral;
                       left-invertible = right-invertible;
                       right-invertible = left-invertible}


  module loop-spaces-are-non-associative-groups (BG : U₀) (e : BG) where

    right-compose-with :
      ∀ {x y z : BG} → 
      (γ : y ≈ z) → (x ≈ y → x ≈ z)
    right-compose-with γ = λ η → η • γ

    right-compose-right-invertible :
      ∀ {x y z : BG}  
      → (γ : x ≈ y)
      → (η : z ≈ y) → (right-compose-with γ) (right-compose-with (γ ⁻¹) η) ≈ η
    right-compose-right-invertible refl refl = refl

    right-compose-left-invertible :
      ∀ {x y z : BG}  
      → (γ : x ≈ y)
      → (η : z ≈ x) → (right-compose-with (γ ⁻¹)) (right-compose-with γ η) ≈ η
    right-compose-left-invertible refl refl = refl

    right-composing-is-an-equivalence :
      ∀ (γ : Ω BG e) → (right-compose-with γ) is-an-equivalence
    right-composing-is-an-equivalence γ =
      has-left-inverse right-compose-with (γ ⁻¹) by right-compose-left-invertible γ
      and-right-inverse right-compose-with (γ ⁻¹) by (λ (η : Ω BG e) → right-compose-right-invertible γ η ⁻¹)


    left-compose-with :
      ∀ {x y z : BG} → 
      (γ : x ≈ y) → (y ≈ z → x ≈ z)
    left-compose-with γ = λ η → γ • η

    left-compose-right-invertible :
      ∀ {x y z : BG}  
      → (γ : x ≈ y)
      → (η : x ≈ z) → (left-compose-with γ) (left-compose-with (γ ⁻¹) η) ≈ η
    left-compose-right-invertible refl refl = refl

    left-compose-left-invertible :
      ∀ {x y z : BG}  
      → (γ : x ≈ y)
      → (η : y ≈ z) → (left-compose-with (γ ⁻¹)) (left-compose-with γ η) ≈ η
    left-compose-left-invertible refl refl = refl

    left-composing-is-an-equivalence :
      ∀ (γ : Ω BG e) → (left-compose-with γ) is-an-equivalence
    left-composing-is-an-equivalence γ =
      has-left-inverse left-compose-with (γ ⁻¹) by left-compose-left-invertible γ
      and-right-inverse left-compose-with (γ ⁻¹) by (λ (η : Ω BG e) → left-compose-right-invertible γ η ⁻¹)


    as-non-associative-group : non-associative-group-structure-on (Ω BG e)
    as-non-associative-group = record { e = refl;
                          μ = λ {(γ , η) → γ • η};
                          left-neutral = refl-is-left-neutral;
                          right-neutral = refl-is-right-neutral ⁻¹⇒;
                          left-invertible = right-composing-is-an-equivalence;
                          right-invertible = left-composing-is-an-equivalence} 


    
