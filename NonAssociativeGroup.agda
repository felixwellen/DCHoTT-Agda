{-# OPTIONS --without-K #-}

module NonAssociativeGroup where 
  open import Basics 
  open import EqualityAndPaths
  open import Homotopies
  open import Language
  open import Equivalences
  open import InfinityGroups
  open import Contractibility
  open import Fiber
  open import EquivalenceCharacterization
  open import Pullback
  open import PullbackSquare

  record non-associative-group-structure-on_ (X : U₀) : U₀ where
    constructor
      structure-given-by-e=_,μ=_,neutral-by_and_,invertible-by_and_
    field
      e : X
      μ : X × X → X
      left-neutral : ∀ (x : X) → μ (e , x) ≈ x
      right-neutral : ∀ (x : X) → μ (x , e) ≈ x
      -- the following means, that for all a,b in X, there is an contractbile space
      -- of x'es such that: xa=b
      -- therefore, 'invertible' may also be called 'cancellable'
      left-invertible : ∀ (x₀ : X) → (λ x → μ (x , x₀)) is-an-equivalence
      right-invertible : ∀ (x₀ : X) → (λ x → μ (x₀ , x)) is-an-equivalence



    open _is-contractible

    -- 'unique' meaning unique up to contractible choice
    uniqueness-of-left-translations :
      (a : X) → (b : X) → (∑ (λ x → μ (x , a) ≈ b)) is-contractible
    uniqueness-of-left-translations a b = types-equivalent-to-contractibles-are-contractible
                                            (fiber-as-sum ⁻¹≃)
                                            (contractible-fibers-characterize-equivalences.to-fiber-condition
                                             (λ x → μ (x , a)) (left-invertible a) b)
    uniqueness-of-right-translations :
      (a : X) → (b : X) → (∑ (λ x → μ (a , x) ≈ b)) is-contractible
    uniqueness-of-right-translations a b = types-equivalent-to-contractibles-are-contractible
                                            (fiber-as-sum ⁻¹≃)
                                            (contractible-fibers-characterize-equivalences.to-fiber-condition
                                             (λ x → μ (a , x)) (right-invertible a) b)

    -- solve equation of the form xa=b
    left-translation-difference : X → X → X
    left-translation-difference a b = ∑π₁ (center (uniqueness-of-left-translations a b))

    left-difference-is-a-solution :
      ∀ (a b : X)
      → μ (left-translation-difference a b , a) ≈ b
    left-difference-is-a-solution a b = ∑π₂ (center (uniqueness-of-left-translations a b))

    right-translation-difference : X → X → X
    right-translation-difference a b = ∑π₁ (center (uniqueness-of-right-translations a b))

    two-solutions-are-equal :
      ∀ {a b : X} (x y : X)
      → μ (x , a) ≈ b → μ (y , a) ≈ b
      → x ≈ y
    two-solutions-are-equal {a} {b} x y γ η =
      let
        c = contraction (uniqueness-of-left-translations a b)
      in ∑π₁ ⁎ (c (x , γ) ⁻¹ • c (y , η))




  -- G-affine types, just some name for something which seems to be
  -- the kind of type having its formal disk bundle trivialized by right translation

--  record _-affine-type {X : U₀} (structure : non-associative-group-structure-on X) : U₀ where
--    field
--      translation : 


  

  module inversion (G : U₀) (structure : non-associative-group-structure-on G) where
    open non-associative-group-structure-on_ structure

--    left-inversion : G → G
--    left-inversion x = {!(left-invertible x) e!}

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


    

  module description-of-∂-pullback {G D : U₀} (structure : non-associative-group-structure-on G) (φ : D → G) where
    open non-associative-group-structure-on_ structure

    ∂ : G × G → G
    ∂ (g , h) = left-translation-difference g h

    left-translate-by-φ : G × D → G × G
    left-translate-by-φ (g , d) = (g , μ (φ(d) , g))

    ∂∘left-translate-by-φ⇒φ∘π₂ : ∂ ∘ left-translate-by-φ ⇒ φ ∘ π₂
    ∂∘left-translate-by-φ⇒φ∘π₂ (g , d) = ∂ (g , μ (φ d , g))
                                        ≈⟨ refl ⟩
                                         left-translation-difference g (μ (φ(d) , g))
                                        ≈⟨ two-solutions-are-equal (left-translation-difference g (μ (φ(d) , g))) (φ(d)) (left-difference-is-a-solution _ _) refl ⟩
                                         φ(d) ≈∎


    ψ : G × D → pullback ∂ φ 
    ψ (g , d) = (( g , μ(φ(d) , g) ) and d are-in-the-same-fiber-by ∂∘left-translate-by-φ⇒φ∘π₂ (g , d))
    
    ψ⁻¹ : pullback ∂ φ  → G × D
    ψ⁻¹ ((g , h) and d are-in-the-same-fiber-by γ) = (g , d)
    
--    result : pullback-square-with-right ∂ bottom φ top left-translate-by-φ left π₂
--    result = the-square-commuting-by ∂∘left-translate-by-φ⇒φ∘π₂ 
--             and-inducing-an-equivalence-by
--               (the-map _ is-an-equivalence-since-it-is-homotopic-to ψ by (λ _ → refl)
--                which-is-an-equivalence-by
--                  (has-left-inverse ψ⁻¹ by (λ _ → refl)
--                   and-right-inverse ψ⁻¹
--                   by (λ {((g , h) and d are-in-the-same-fiber-by γ)
--                       →  ((g , h) and d are-in-the-same-fiber-by γ)
--                         ≈⟨ {!!}⟩
--                          (( g , μ(φ(d) , g) ) and d are-in-the-same-fiber-by ∂∘left-translate-by-φ⇒φ∘π₂ (g , d))
--                         ≈∎})))
    
