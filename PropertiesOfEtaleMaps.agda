{-# OPTIONS --without-K #-}

module PropertiesOfEtaleMaps where 
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Equivalences renaming (underlying-map-of to underlying-map-of-the-equivalence)
  open import Pullback
  open import PullbackSquare
  open import DependentTypes
  open import Im
  open import Language
  open import EtaleMaps
  open import FormalDisk
  open import FormalDiskBundle

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

    conclusion-as-equivalence-above-the-map :
      equivalence-of (𝔻 A) and (𝔻 B) over f
    conclusion-as-equivalence-above-the-map x =
      let
        open pullbacks-are-fiberwise-equivalences conclusion
        step1 = pullback-definition-and-dependent-version-agree.on-fibers A
        step2 = pullback-definition-and-dependent-version-agree.on-fibers B
      in (step2 (f x)) ∘≃ (equivalence-at x) ∘≃ (step1 x ⁻¹≃)


  -- composition of etale maps
{-
  the-composition-of-the-maps_and_being-étale-by_and_is-étale :
    ∀ {A B C : U₀} 
    → (g : B → C) → (f : A → B) → (g is-étale) → (f is-étale)
    → (g ∘ f) is-étale
  the-composition-of-the-maps g and f being-étale-by g-is-étale and f-is-étale is-étale =
    the-induced-map-is-an-equivalence-by 
      (the-induced-map-in pasted-squares-for-f-and-g is-an-equivalence)
    where pasted-squares-for-f-and-g = {!substitute-homotopic-bottom-map (pasting-of-pullback-squares 
      (rotate-cospan (pullback-square-for-the-étale-map (g , g-is-étale))) 
      (rotate-cospan (pullback-square-for-the-étale-map (f , f-is-étale)))) (ℑ→ (g ∘ f)) ?!}


  infixr 70 _∘ét_
  _∘ét_ : ∀ {A B C : U₀} 
    → (B ─ét→ C) → (A ─ét→ B) → (A ─ét→ C)
  g ∘ét f = {!!}
  
-}
