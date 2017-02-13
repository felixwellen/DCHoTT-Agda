{-# OPTIONS --without-K #-}
{- read the README -}

module FormalDiskBundle where 
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Language
  open import Equivalences
  open import CommonEquivalences
  open import Pullback
  open import PullbackSquare
  open import Im
  open import InfinityGroups
  open import MayerVietoris
  open import EtaleMaps hiding (underlying-map-of)
  open import NonAssociativeGroup

  _is-infinitesimally-close-to_ :
    {X : U₀} → (x x′ : X) → U₀
  x is-infinitesimally-close-to x′ = ℑ-unit x ≈ ℑ-unit x′

  -- T∞ as dependent type
  formal-disk-at_ :
    ∀ {X : U₀}
    → (x : X) → (X → U₀)
  formal-disk-at_ x x′ = x′ is-infinitesimally-close-to x

  T∞′ : ∀ (X : U₀) 
    → (X → U₀)
  T∞′ X x = ∑ (formal-disk-at x)

  formal-disk-bundle : (X : U₀) → U₀
  formal-disk-bundle X = pullback (ℑ-unit-at X) (ℑ-unit-at X)

  T∞ : (X : U₀) → U₀
  T∞ X = formal-disk-bundle X

  p-of-T∞ : (X : U₀) → (T∞ X) → X
  p-of-T∞ X = p₁-of-pullback (ℑ-unit-at X) (ℑ-unit-at X)

  formal-disk-bundle-as-pullback-square :
    ∀ (X : U₀) → pullback-square-with-right ℑ-unit bottom ℑ-unit top p₁ left p₂
  formal-disk-bundle-as-pullback-square X = complete-to-pullback-square (ℑ-unit-at X) (ℑ-unit-at X)



  module triviality-of-the-formel-disk-bundle-over-∞-groups (BG : U₀) (e : BG) where
    G = Ω BG e

    ℑG = ℑ G
    ℑG′ = Ω (ℑ BG) (ℑ-unit e)

    structure-on-G = loop-spaces-are-non-associative-groups.as-non-associative-group BG e
    structure-on-ℑG = ℑ-preserves-non-associative-groups.structure-of-image G structure-on-G

    ℑGΔ′ : ℑG′ × ℑG′ → ℑG′
    ℑGΔ′ = ∞-group-Δ (ℑ BG) (ℑ-unit e) 

    disk-to-coreduced-point : T∞ G → ℑG
    disk-to-coreduced-point (a and b are-in-the-same-fiber-by γ) = ℑ-unit a 

    forget-path : T∞ G → G × G
    forget-path (g and h are-in-the-same-fiber-by _) = (g , h)

  -- 
  -- Step 1:
  -- T∞ G --→ G        T∞ G  -→ ℑG
  --   |  ⌟   |          |  ⌟    |
  --   |      |   ⇒      |       Δ
  --   ↓      ↓          ↓       ↓
  --   G --→ ℑG       G × G → ℑG × ℑG

    step1′ : pullback-square-with-right Δ
              bottom (ℑ-unit-at G ×→ ℑ-unit-at G) 
              top (proof-of-mayer-vietoris-part-1.ν G G ℑG ℑ-unit ℑ-unit) 
              left (proof-of-mayer-vietoris-part-1.θ G G ℑG ℑ-unit ℑ-unit) 
    step1′ = proof-of-mayer-vietoris-part-1.as-pullback-square G G ℑG ℑ-unit
              ℑ-unit

    -- substitute the maps defined in this file
    step1″ : pullback-square-with-right Δ
             bottom (ℑ-unit-at G ×→ ℑ-unit-at G) 
             top disk-to-coreduced-point
             left forget-path
    step1″ = substitute-equivalent-cone disk-to-coreduced-point forget-path id
              id-is-an-equivalence 
              (λ {(_ and _ are-in-the-same-fiber-by _) → refl}) 
              (λ {(_ and _ are-in-the-same-fiber-by _) → refl}) 
              step1′



    step1 : pullback-square-with-right Δ
             bottom (ℑ-unit-at G ×→ ℑ-unit-at G) 
             top disk-to-coreduced-point
             left forget-path
    step1 = equality-of-squares-preserve-the-pullback-property
               step1″ (λ { (_ and _ are-in-the-same-fiber-by γ) → ×-create-equality refl γ })
                     (λ { (_ and _ are-in-the-same-fiber-by _) → refl-is-right-neutral _ })

    {-   Step 2:
       use mayer-vietoris-lemma on oo-group like structures to get a square:

      ℑG ---→ ∗
       |  ⌟   |
       Δ      |
       ↓      ↓
    ℑG × ℑG → ℑG′
  
  -}
    open non-associative-group-structure-on_ structure-on-G using (∂; μ) 
    open non-associative-group-structure-on_ structure-on-ℑG using ()
         renaming (∂ to ℑ∂; e to ℑe; μ to ℑμ; left-neutral to ℑleft-neutral) 

    constant-ℑe : One → ℑG
    constant-ℑe x = ℑe


    square2a : 
          pullback-square-with-right constant-ℑe
              bottom ℑ∂
              top π₁
              left (λ {(d , g) → (g , ℑμ (ℑe , g))})
    square2a = mayer-vietoris-lemma.result-as-square structure-on-ℑG
                     constant-ℑe
    

    constant-∗′ : ℑG → One
    constant-∗′ _ = ∗

    square2 :
          pullback-square-with-right constant-ℑe
              bottom ℑ∂
              top constant-∗′
              left Δ
    square2 = substitute-equivalent-cone
                    constant-∗′ Δ
                    (λ g → ∗ , g) (has-left-inverse π₂ by (λ _ → refl) and-right-inverse π₂ by (λ {(∗ , _) → refl}))
                    (λ _ → refl) (λ g → (λ x → g , x) ⁎ ℑleft-neutral g)
                    square2a

    {-
      Step 3 (combine square 1 and 2):

       T∞ G  -→ ℑG           ℑG ----→ ∗      T∞ G ---→ ∗
        |  ⌟    |             |  ⌟    |        |  ⌟    |
        |       Δ      and    Δ       |   ⇒    |       |
        ↓       ↓             ↓       ↓        ↓       ↓
     G × G → ℑG × ℑG       ℑG × ℑG → ℑG      G × G --→ ℑG
    
    -}

    square3 : 
      pullback-square-with-right constant-ℑe
        bottom ℑ∂ ∘ (ℑ-unit ×→ ℑ-unit)
        top (λ _ → ∗)
        left forget-path
    square3 = pasting-of-pullback-squares step1 square2
    

    {-
  
    Step 4: factor square3

             T∞ G ────────→ ∗
              | ⌟           |
 forget-path  |             |
              ↓             ↓
            G × G --→ G -→ ℑG
              \       ⇓    ↗ 
               ─ ℑ-unit ∘ ∂  
    -}

    square4 = substitute-homotopic-bottom-map square3
                (ℑ-unit ∘ ∂)
                (ℑ-preserves-non-associative-groups.ℑ∂-square G structure-on-G)

    De = D G (refl {a = e})

    φ : De → G
    φ = p₂

    {-
  
    the right square
      
     De -→ ∗
     | ⌟   |
     |     |
     ↓     ↓
     G -→ ℑG
    
    -}
    
    new-De-square : pullback-square-with-right (λ _ → ℑe)
                      bottom ℑ-unit
                      top p₁
                      left φ
    new-De-square = complete-to-pullback-square (λ ∗ → ℑe) (ℑ-unit-at G)



    {- 
    Step 5: Conclude, that the left square
     T∞ G ---→ De
      | ⌟      |
      |        φ 
      ↓        ↓ 
    G × G -∂G→ G

    is a pullback
    -}

    square5 : pullback-square-with-right φ
                bottom ∂
                top _
                left forget-path
    square5 = cancel-the-right-pullback-square new-De-square from square4


    {- Step 6a: Same cospan 'different' pullback

     De × G --> De
       | ⌟      |
       |        φ
       ↓        ↓
     G × G -∂-> G
    
    -}

    square6 : pullback-square-with-right φ 
                bottom ∂
                top π₁
                left (λ {(d , g) → (g , μ ((φ d) , g))})
    square6 = mayer-vietoris-lemma.result-as-square structure-on-G φ


    -- Step6b: deduce equivalence ∎

    step6 : De × G ≃ T∞ G
    step6 = deduce-equivalence-of-vertices square6 square5

    step6′ : T∞ G ≃ De × G
    step6′ = deduce-equivalence-of-vertices square5 square6
    
    as-product-square :
      pullback-square-with-right (λ (d : De) → ∗)
        bottom (λ (g : G) → ∗)
        top _
        left p₁
    as-product-square = 
      square6 and square5 pull-back-the-same-cospan-so-the-first-may-be-replaced-by-the-second-in-the-square (product-square De G)
      
