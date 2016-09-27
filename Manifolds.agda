{-# OPTIONS --without-K #-}

module Manifolds where 
  open import Basics 
  open import EqualityAndPaths
  open import PropositionalTruncation
  open import Equivalences renaming (underlying-map-of to underlying-map-of-the-equivalence)
  open import Pullback
  open import PullbackSquare
  open import InfinityGroups
  open import Contractibility
  open import Homotopies
  open import Im
  open import FormalDiscBundle
  open import EtaleMaps
  open import Language
  open import OneImage

  pullback-square-of :
    ∀ {A B : U₀}
    → (f́ : A ─ét→ B) 
    → pullback-square-with-right (apply-ℑ-to-map (underlying-map-of f́))
        bottom ℑ-unit
        top ℑ-unit
        left (underlying-map-of f́)
  pullback-square-of (f , pullback-property) =
    commutes-by naturality-of-ℑ-unit f
      and-the-induced-map-is-an-equivalence-by pullback-property

  _is-a-manifold-by-the-covering_which-is-a-covering-of-the-∞-group-with-delooping_,_by_ : 
    ∀ {W : U₀} (M : U₀)
    → (χ : W ─ét→ M) → (BG : U₀) (e : BG) → (ξ : W ─ét→ Ω BG e)
    → U₀
  M is-a-manifold-by-the-covering χ which-is-a-covering-of-the-∞-group-with-delooping BG , e by ξ =
    underlying-map-of χ is-surjective

  module formal-disk-bundles-are-preserved-by-étale-base-change {A B : U₀} (f́ : A ─ét→ B) where

    f = underlying-map-of f́

    {-
    Step 1a: formal disk bundle on the codaim as a pullback square
    
    T∞ B ──→ B
     | ⌟     |
     |       |
     ↓       ↓
     B ───→ ℑ B

    -}

    step1a : pullback-square-with-right ℑ-unit 
               bottom ℑ-unit 
               top p₁ 
               left p₂
    step1a = formal-disk-bundle-as-pullback-square B

    {-
    Step 1b: base change along f as pullback square

    f*T∞ B ──→ T∞ B
       | ⌟      |
       |        |
       ↓        ↓
       A ──ét─→ B
    -}

    step1b : pullback-square-with-right p₂
               bottom f
               top p₁
               left p₂
    step1b = complete-to-pullback-square 
               (p₂-of-pullback ℑ-unit ℑ-unit)
               f

    {-
    Step 2: Since f́ is étale, we have a pullback square

       A ──────→ B 
       | ⌟       |     
       |         |
       ↓         ↓
      ℑ A ─ℑf─→ ℑ B

    -}
    step2 = rotate-cospan (pullback-square-of f́)

    {-
    Step 3: Compose with the T∞-square for A to get
     T∞ A ─────→ B 
       | ⌟       |     
       |         |
       ↓         ↓
       A ──ηf─→ ℑ B
 
    -}
    step3 : pullback-square-with-right (ℑ-unit-at B)
               bottom (ℑ-unit ∘ f)
               top _
               left (p₂-of-pullback (ℑ-unit-at A) (ℑ-unit-at A))
    step3 = substitute-homotopic-bottom-map 
               (pasting-of-pullback-squares 
                 step2 
                 (formal-disk-bundle-as-pullback-square A)) 
               (ℑ-unit ∘ f)
               (naturality-of-ℑ-unit f ⁻¹∼)

    {-
    Conclude by cancelling with step1:
     T∞ A ──→ T∞ B 
       | ⌟     |     
       |       |
       ↓       ↓
       A ──f─→ B
      
    -}

    conclusion : pullback-square-with-right (p-of-T∞ B)
        bottom f
        top _
        left (p-of-T∞ A)
    conclusion = cancel-the-right-pullback-square step1a from step3

    f*T∞B = upper-left-vertex-of step1b

    conclusion-as-equivalence : f*T∞B ≃ T∞ A
    conclusion-as-equivalence = deduce-equivalence-of-vertices 
                                  step1b
                                  conclusion


  _is-locally-trivial-over_by_with-fiber_ :
    ∀ {E M : U₀}
    → (φ : E → M) → (V : U₀) → (v : V ─ét→ M) → (D : U₀) → U₀
  φ is-locally-trivial-over V by v with-fiber D =
    pullback-square-with-right (λ (d : D) → ∗) bottom (λ (v₁ : V) → ∗)
      top π₂ left π₁

  -- product property expressed by pullback square
  _is-a-product-with-projections_and_ :
    ∀ {A B : U₀} (Z : U₀) (z₁ : Z → A) (z₂ : Z → B)
    → U₀
  Z is-a-product-with-projections z₁ and z₂ =
    pullback-square-with-right (λ a → ∗)
        bottom (λ b → ∗)
        top z₁
        left z₂

  _is-a-product-of_and_ :
    (Z A B : U₀) → U₀
  Z is-a-product-of A and B =
    ∑ (λ (z₁ : Z → A) →
    ∑ (λ (z₂ : Z → B) → Z is-a-product-with-projections z₁ and z₂))

  _*_ : ∀ {E B B′ : U₀}
    → (f : B′ → B) → (φ : E → B) → U₀
  f * φ = upper-left-vertex-of (complete-to-pullback-square φ f)
  
  _*→_ : ∀ {E B B′ : U₀}
    → (f : B′ → B) → (φ : E → B) → ((f * φ) → B′)
  f *→ φ = left-map-of (complete-to-pullback-square φ f)

  ^ = underlying-map-of-the-surjectiveism

  record _is-a_-fiber-bundle {E B : U₀} (φ : E → B) (F : U₀) : U₁ where
    constructor on_the-pullback-along_is-trivial-by_and_
    field
      V : U₀
      covering : V ↠ B
      projection-to-the-fiber : (^ covering * φ) → F
      the-pullback-is-a-product :
          (^ covering * φ) is-a-product-with-projections
            projection-to-the-fiber and (^ covering *→ φ) 

  module the-formal-disk-bundle-on-a-manifold-is-a-fiber-bundle 
         (V M : U₀) (v́ : V ─ét→ M) 
         (BG : U₀) (e : BG) (ǵ : V ─ét→ Ω BG e)
         (M-is-a-manifold : M is-a-manifold-by-the-covering v́ 
                            which-is-a-covering-of-the-∞-group-with-delooping BG , e
                            by ǵ) where

         v = underlying-map-of v́
         g = underlying-map-of ǵ
         G = Ω BG e
         De = D G refl


         {-
         T∞ V is a trivial bundle, which is witnessed by the square
         
         T∞V ───→ De
          | ⌟     |
          |       |
          ↓       ↓
          V ────→ 1

         constructed below
         -}
         T∞V-is-trivial : 
           pullback-square-with-right (λ (d : De) → ∗)
             bottom (λ (x : V) → ∗)
             top _
             left (p-of-T∞ V)
         T∞V-is-trivial =
           pasting-of-pullback-squares 
             (substitute-homotopic-left-map
               (triviality-of-the-formel-disk-bundle-over-∞-groups.as-product-square BG e) 
               p₂ (λ {(g₁ and g₂ are-in-the-same-fiber-by γ) → refl}))
             (formal-disk-bundles-are-preserved-by-étale-base-change.conclusion ǵ)  

         T∞V-is-equivalent-to-v*T∞M :
           pullback-square-with-right (p-of-T∞ V)
             bottom id
             top _
             left _
         T∞V-is-equivalent-to-v*T∞M =
           (formal-disk-bundles-are-preserved-by-étale-base-change.conclusion v́)
           and (complete-to-pullback-square (p-of-T∞ M) v)
           pull-back-the-same-cospan-so-the-first-may-be-replaced-by-the-second-in-the-square
           (pullback-square-from-identity-of-morphisms (p-of-T∞ V))

         v*T∞M-is-trivial :
           pullback-square-with-right (λ (d : De) → ∗)
             bottom (λ (x : V) → ∗)
             top _
             left (v *→ (p-of-T∞ M))
         v*T∞M-is-trivial =
           substitute-homotopic-left-map
             (pasting-of-pullback-squares
               T∞V-is-trivial
               T∞V-is-equivalent-to-v*T∞M)
             (v *→ (p-of-T∞ M))
             (deduced-equivalence-factors-the-left-map
                (complete-to-pullback-square (p-of-T∞ M) v)
                (formal-disk-bundles-are-preserved-by-étale-base-change.conclusion
                 v́)
                ⁻¹⇒)

         
         T∞M-is-a-fiber-bundle : (p-of-T∞ M) is-a De -fiber-bundle
         T∞M-is-a-fiber-bundle =
           let
             v́-as-surjectiveism = (v is-surjective-by M-is-a-manifold)
           in
             on V the-pullback-along v́-as-surjective-map
             is-trivial-by top-map-of v*T∞M-is-trivial
             and v*T∞M-is-trivial
