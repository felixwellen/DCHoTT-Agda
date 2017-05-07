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
  open import LeftInvertibleHspace
  open import DependentTypes

  _is-infinitesimally-close-to_ :
    {X : U₀} → (x x′ : X) → U₀
  x is-infinitesimally-close-to x′ = ℑ-unit x ≈ ℑ-unit x′

  _is-close-to_ :
    {X : U₀} → (x x′ : X) → U₀
  _is-close-to_ = _is-infinitesimally-close-to_

  mapping-with_preserves-infinitesimal-proximity :
    ∀ {X Y : U₀} {x x′ : X}
    → (f : X → Y)
    → (x is-close-to x′) → (f x) is-close-to (f x′)
  mapping-with f preserves-infinitesimal-proximity γ = ℑ⁎ f ⁎ γ  -- see 'Im.agda'
  
  -- T∞ as dependent type
  formal-disk-at_ :
    ∀ {X : U₀}
    → (x : X) → U₀
  formal-disk-at x = ∑ (λ x′ → x is-close-to x′)

  induced-map-on-formal-disks :
    ∀ {X Y : U₀}
    → (f : X → Y)
    → (x : X) → formal-disk-at x → formal-disk-at (f x)
  induced-map-on-formal-disks f x (x′ , x′-is-close-to-x) =
    (f x′ , mapping-with f preserves-infinitesimal-proximity x′-is-close-to-x)

  T∞→ = induced-map-on-formal-disks

  formal-disk-bundle : (X : U₀) → U₀
  formal-disk-bundle X = pullback (ℑ-unit-at X) (ℑ-unit-at X)

  T∞ : (X : U₀) → U₀
  T∞ X = formal-disk-bundle X

  T∞-as-dependent-type :
    (X : U₀) → X → U₀
  T∞-as-dependent-type X x = formal-disk-at x 
  
  p-of-T∞ : (X : U₀) → (T∞ X) → X
  p-of-T∞ X = p₁-of-pullback (ℑ-unit-at X) (ℑ-unit-at X)

  formal-disk-bundle-as-pullback-square :
    ∀ (X : U₀) → pullback-square-with-right ℑ-unit bottom ℑ-unit top p₁ left p₂
  formal-disk-bundle-as-pullback-square X = complete-to-pullback-square (ℑ-unit-at X) (ℑ-unit-at X)

  {-
    we have two versions of the disk bundle, 
    one constructed as a pullback, the other
    as the sum over the T∞-as-dependent-type
  -}
  module pullback-definition-and-dependent-version-agree (X : U₀) where

    φ : T∞ X → ∑ (T∞-as-dependent-type X)
    φ (x and y are-in-the-same-fiber-by γ) = (x , (y , γ))

    φ⁻¹ : ∑ (T∞-as-dependent-type X) → T∞ X
    φ⁻¹ (x , (y , γ)) = x and y are-in-the-same-fiber-by γ

    conclusion : T∞ X ≃ ∑ (T∞-as-dependent-type X)
    conclusion = φ is-an-equivalence-because
      (has-left-inverse φ⁻¹ by (λ _ → refl)
       and-right-inverse φ⁻¹ by (λ _ → refl))

  {-
    Above, for a morphism f : A → B, we defined the induced
    dependent morphism  T∞ f : (a : A) → formal-disk-at a → formal-disk-at (f a)
    if f is an equivalence, T∞ f is an equivalence.
  -}

  module equivalences-induce-equivalences-on-formal-disks
    {A B : U₀} (f≃ : A ≃ B) where

    f = underlying-map-of f≃

    ℑf⁎-is-an-equivalence : (x y : A) → (λ (γ : x is-close-to y) → ℑ⁎ f ⁎ γ) is-an-equivalence
    ℑf⁎-is-an-equivalence = equivalences-induce-equivalences-on-the-coreduced-identity-types.ℑf⁎-is-an-equivalence f≃
    
    T∞f-is-an-equivalence : (a : A) → (T∞→ f a) is-an-equivalence
    T∞f-is-an-equivalence a =
      fiber-equivalences-along-an-equivalence-on-the-base.induced-map-is-an-equivalence
        (λ x → a is-close-to x) (λ y → f a is-close-to y) f≃
        (λ x →
           (λ (γ : a is-close-to x) → ℑ⁎ f ⁎ γ) is-an-equivalence-because
           ℑf⁎-is-an-equivalence a x)
           
    conclusion : (a : A) → formal-disk-at a ≃ formal-disk-at (f a)
    conclusion a = (T∞→ f a) is-an-equivalence-because (T∞f-is-an-equivalence a)

  module paths-induce-equivalences-of-formal-disks
    {A : U₀} {x y : A} (γ : x ≈ y) where

    transport-in-T∞ :
      formal-disk-at x ≃ formal-disk-at y
    transport-in-T∞ = transport-as-equivalence (T∞-as-dependent-type A) γ

    conclusion = transport-in-T∞


  {-
    this is a new proof for the triviality of T∞ over left-invertible H-spaces
    in contrast to the second proof below, it needs univalence
  -}
  module triviality-of-the-formel-disk-bundle-using-univalence
    {V : U₀} (structure-on-V : left-invertible-structure-on V) where

    open left-invertible-structure-on_ structure-on-V

    De : U₀
    De = formal-disk-at e

    equivalences : (x : V) → De ≃ formal-disk-at x
    equivalences x =
        paths-induce-equivalences-of-formal-disks.conclusion
          (left-neutral x)
      ∘≃
        equivalences-induce-equivalences-on-formal-disks.conclusion
          (right-translation x) e

    {- 
      now, univalences turns this family to a homotopy in the universe
      from the disk-bundle on V to the map constantly De
    -}
    open import Univalence

    constant-family : V → U₀
    constant-family v = De

    the-homotopy : constant-family ⇒ (T∞-as-dependent-type V)
    the-homotopy v = univalence (equivalences v)
    

  module triviality-of-the-formel-disk-bundle-over-∞-groups
    {G : U₀} (structure-on-G : left-invertible-structure-on G) where

    ℑG = ℑ G

    structure-on-ℑG = ℑ-preserves-left-invertible-H-spaces.structure-of-image G structure-on-G

    open left-invertible-structure-on_ structure-on-G using (∂; μ; e) 
    open left-invertible-structure-on_ structure-on-ℑG using ()
         renaming (∂ to ℑ∂; e to ℑe; μ to ℑμ; left-neutral to ℑleft-neutral) 

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
                (ℑ-preserves-left-invertible-H-spaces.ℑ∂-square G structure-on-G)

    De = D G e

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
      
