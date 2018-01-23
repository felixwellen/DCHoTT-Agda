{-# OPTIONS --without-K #-}

module Manifolds where 
  open import Basics 
  open import EqualityAndPaths
  open import PropositionalTruncation
  open import DependentTypes
  open import Fiber
  open import Equivalences renaming (underlying-map-of to underlying-map-of-the-equivalence)
  open import Pullback
  open import PullbackSquare
  open import InfinityGroups
  open import Contractibility
  open import Homotopies
  open import Im
  open import FormalDiskBundle
  open import EtaleMaps
  open import Language
  open import OneImage
  open import FiberBundle
  open import FormalDisk
  open import HomogeneousType

  pullback-square-of :
    ∀ {A B : U₀}
    → (f́ : A ─ét→ B) 
    → pullback-square-with-right (ℑ→ (underlying-map-of f́))
        bottom ℑ-unit
        top ℑ-unit
        left (underlying-map-of f́)
  pullback-square-of (f , (the-induced-map-is-an-equivalence-by pullback-property)) =
    the-square-commuting-by (naturality-of-ℑ-unit f)
      and-inducing-an-equivalence-by pullback-property

  _is-a-manifold-with-cover_locally-like_by_ : 
    ∀ {W : U₀} {V : U₀} (M : U₀)
    → (w : W ─ét→ M) → (structure-on-V : homogeneous-structure-on V) → (v : W ─ét→ V)
    → U₀
  M is-a-manifold-with-cover w locally-like structure-on-V by v =
    underlying-map-of w is-1-epi

  left-invertible-H-spaces-are-manifolds :
    ∀ {V : U₀} (structure-on-V : homogeneous-structure-on V)
    → V is-a-manifold-with-cover id-as-étale-map locally-like structure-on-V by id-as-étale-map
  left-invertible-H-spaces-are-manifolds _ = equivalences-are-1-epi id-as-equivalence
  
  module formal-disk-bundles-are-preserved-by-étale-base-change {A B : U₀} (f́ : A ─ét→ B) where

    f = underlying-map-of f́

    {-
    Step 1a: formal disk bundle on the codomain as a pullback square
    
    T∞ B ──→ B
     | ⌟     |
     |       |
     ↓       ↓
     B ───→ ℑ B

    -}

    step1a : pullback-square-with-right ℑ-unit 
               bottom ℑ-unit 
               top p₂ 
               left p₁
    step1a = rotate-cospan (formal-disk-bundle-as-pullback-square B)

    {-
    Step 1b: base change along f as pullback square

    f*T∞ B ──→ T∞ B
       | ⌟      |
       |        |
       ↓        ↓
       A ──ét─→ B
    -}

    step1b : pullback-square-with-right (p-of-T∞ B)
               bottom f
               top _
               left _
    step1b = complete-to-pullback-square 
               (p-of-T∞ B)
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
               left (p-of-T∞ A)
    step3 = substitute-homotopic-bottom-map
               (pasting-of-pullback-squares 
                 (rotate-cospan (formal-disk-bundle-as-pullback-square A))
                 step2)
                 (ℑ-unit ∘ f) ((naturality-of-ℑ-unit f ⁻¹∼))
                  
             

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





  module the-formal-disk-bundle-on-a-manifold-is-a-fiber-bundle 
         {V : 𝒰} (U M : 𝒰) (w : U ─ét→ M) 
         (structure-on-V : homogeneous-structure-on V) (v : U ─ét→ V)
         (M-is-a-manifold : M is-a-manifold-with-cover w
                            locally-like structure-on-V by v) where

         open homogeneous-structure-on_ structure-on-V
         𝔻ₑ = 𝔻 V e -- formal-disk-at e

         {-

         T∞ U is a trivial bundle, which is witnessed by the square
         
         T∞U ───→ 𝔻ₑ
          | ⌟     |
          |       |
          ↓       ↓
          U ────→ 1

         constructed below

         -}

         T∞U-is-trivial : 
           pullback-square-with-right (λ (d : 𝔻ₑ) → ∗)
             bottom (λ (x : U) → ∗)
             top _
             left (p-of-T∞ U)
         T∞U-is-trivial =
           pasting-of-pullback-squares 
             (formal-disk-bundles-are-preserved-by-étale-base-change.conclusion v)  
             (triviality-of-the-formal-disk-bundle-over-homogeneous-types.as-product-square
               structure-on-V)

         {-

            T∞U─id─→T∞U 
             | ⌟     |   
             p       p   and ? 
             |       |
             ↓       ↓
             U ─id─→ U

         -}

         T∞U-is-equivalent-to-w*T∞M :
           pullback-square-with-right (p-of-T∞ U)
             bottom id
             top _
             left _
         T∞U-is-equivalent-to-w*T∞M =
           (formal-disk-bundles-are-preserved-by-étale-base-change.conclusion w)
           and (complete-to-pullback-square (p-of-T∞ M) (underlying-map-of w))
           pull-back-the-same-cospan-so-the-first-may-be-replaced-by-the-second-in-the-square
           (pullback-square-from-identity-of-morphisms (p-of-T∞ U))

         w*T∞M-is-trivial :
           pullback-square-with-right (λ (d : 𝔻ₑ) → ∗)
             bottom (λ (x : U) → ∗)
             top _
             left ((underlying-map-of w) *→ (p-of-T∞ M))
         w*T∞M-is-trivial =
           substitute-homotopic-left-map
             (pasting-of-pullback-squares
               T∞U-is-equivalent-to-w*T∞M
               T∞U-is-trivial)
             ((underlying-map-of w) *→ (p-of-T∞ M))
             (deduced-equivalence-factors-the-left-map
                (complete-to-pullback-square (p-of-T∞ M) (underlying-map-of w))
                (formal-disk-bundles-are-preserved-by-étale-base-change.conclusion
                 w)
                ⁻¹⇒)

         
         T∞M-is-a-fiber-bundle : (p-of-T∞ M) is-a′ 𝔻ₑ -fiber-bundle′
         T∞M-is-a-fiber-bundle =
           let
             v́-as-surjection = (underlying-map-of w) is-1-epi-by M-is-a-manifold
           in
             on U the-pullback-along v́-as-surjection
             is-trivial-by top-map-of w*T∞M-is-trivial
             and w*T∞M-is-trivial

         classifying-morphism : M → BAut 𝔻ₑ
         classifying-morphism =
           all-fiber-bundle-are-associated.classifying-morphism (p-of-T∞ M) T∞M-is-a-fiber-bundle


         commutes-with-the-dependent-replacement-of-T∞′ :
           (dependent-replacement (p-of-T∞ M)) ⇒ (ι-BAut 𝔻ₑ) ∘ classifying-morphism 
         commutes-with-the-dependent-replacement-of-T∞′ x =
           all-fiber-bundle-are-associated.as-U₀-morphism (p-of-T∞ M)
             T∞M-is-a-fiber-bundle x

         -- the following makes a probably unnecessary use of univalence
         open import Univalence
         commutes-with-the-dependent-replacement-of-T∞ :
           (λ (x : M) → 𝔻 _ x) ⇒ (ι-BAut 𝔻ₑ) ∘ classifying-morphism
         commutes-with-the-dependent-replacement-of-T∞ x =
             𝔻 _ x
           ≈⟨ univalence
                (pullback-definition-and-dependent-version-agree.on-fibers M x ⁻¹≃) ⟩
             (dependent-replacement (p-of-T∞ M)) x
            ≈⟨ commutes-with-the-dependent-replacement-of-T∞′ x ⟩
             ((ι-BAut 𝔻ₑ) ∘ classifying-morphism) x
           ≈∎


         -- conclude, that the formal disks are equivalent
         all-formal-disks-are-merely-equivalent :
           ∀ (x : M)
           → ∥ 𝔻ₑ ≃ formal-disk-at x ∥
         all-formal-disks-are-merely-equivalent x =
           let
             ψ : fiber-of (p-of-T∞ M) at x ≃ formal-disk-at x 
             ψ = pullback-definition-and-dependent-version-agree.on-fibers M x
           in ∥→ (λ (f : 𝔻ₑ ≃ (fiber-of p-of-T∞ M at x)) → ψ ∘≃ f) ∥→ 
            (all-fiber-bundle-are-associated.all-fibers-are-merely-equivalent
              (p-of-T∞ M) T∞M-is-a-fiber-bundle x)
