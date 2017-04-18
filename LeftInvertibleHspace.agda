{-# OPTIONS --without-K #-}

module LeftInvertibleHspace where 
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
  open import Sums

  record left-invertible-structure-on_ (X : U₀) : U₀ where
    constructor
      structure-given-by-e=_,μ=_,neutral-by_and_,left-invertible-by_and_
    field
      e : X
      μ : X × X → X
      left-neutral : ∀ (x : X) → μ (e , x) ≈ x
      right-neutral : ∀ (x : X) → μ (x , e) ≈ x
      -- the following means, that for all a,b in X, there is an contractible space
      -- of x'es such that: xa=b
      -- therefore, 'invertible' may also be called 'cancellable'
      left-invertible : ∀ (x₀ : X) → (λ x → μ (x , x₀)) is-an-equivalence

  
    

    open _is-an-equivalence 
    
    left-invert : ∀ (x₀ : X) → (X → X)
    left-invert x₀ = left-inverse (left-invertible x₀)

    left-inverting-is-an-equivalence : ∀ (x₀ : X) → (left-invert x₀) is-an-equivalence
    left-inverting-is-an-equivalence x₀ = the-inverse-of (λ x → μ (x , x₀)) which-is-an-equivalence-by
                                            (left-invertible x₀) is-again-an-equivalence

    open _is-contractible
    open import CommonEquivalences 
    -- 'unique' meaning unique up to contractible choice
    uniqueness-of-left-translations :
      (a : X) → (b : X) → (∑ (λ x → μ (x , a) ≈ b)) is-contractible
    uniqueness-of-left-translations a b = types-equivalent-to-contractibles-are-contractible
                                            (fiber-as-sum ⁻¹≃)
                                            (contractible-fibers-characterize-equivalences.to-fiber-condition
                                             (λ x → μ (x , a)) (left-invertible a) b)

    uniqueness-of-left-translations′ :
      (a : X) → (b : X) → (∑ (λ x → b ≈ μ (x , a))) is-contractible
    uniqueness-of-left-translations′ a b =
       types-equivalent-to-contractibles-are-contractible
          (the-equivalence-of-sums-given-by (λ _ γ → γ ⁻¹)
            being-fiberwise-an-equivalence-by (λ _ → inversion-is-an-equivalence.proof))
          (uniqueness-of-left-translations a b)
    

    -- solve equation of the form xa=b
    left-translation-difference : X → X → X
    left-translation-difference a b = left-invert a b

    infix 50 _‣_
    _‣_ : X → X → X
    a ‣ b = μ (a , b)

    _‣_⁻ : X → X → X
    a ‣ b ⁻ = left-translation-difference b a

    -- read as difference
    ∂ : X × X → X
    ∂ (a , b) = b ‣ a ⁻

    ∂-is-left-inverse-of-right-translation :
      ∀ (a : X)
      → (λ (x : X) → x ‣ a ⁻) ∘ (λ x → x ‣ a) ⇒ id
    ∂-is-left-inverse-of-right-translation a = unit (left-invertible a)

    ∂-is-right-inverse-of-right-translation :
      ∀ (a : X)
      →  (λ x → x ‣ a) ∘ (λ (x : X) → x ‣ a ⁻) ⇒ id
    ∂-is-right-inverse-of-right-translation a =
      left-inverses-are-also-right-inverses (λ x → x ‣ a)
        (λ (x : X) → x ‣ a ⁻) _ (∂-is-left-inverse-of-right-translation a)
        (counit (left-invertible a))

    -- the following stuff finds its non-obvious use in Im.agda

    invertibilty-as-automorphism-of-the-product :
      (π₂ ,→ μ) is-an-equivalence
    invertibilty-as-automorphism-of-the-product =
      has-left-inverse (∂ ,→ π₁)
        by (λ {(a , b) → (λ x → (x , b)) ⁎ ∂-is-left-inverse-of-right-translation b a})
      and-right-inverse (∂ ,→ π₁)
        by (λ {(a , b) → (λ x → a , x) ⁎ ∂-is-right-inverse-of-right-translation a b ⁻¹})

    ∂-triangle :
      π₁ ⇒ ∂ ∘ (π₂ ,→ μ)
    ∂-triangle (a , b) = ∂-is-left-inverse-of-right-translation b a ⁻¹
    
    ∂-is-determined-by-a-triangle :
      ∀ (f : X × X → X)
      → π₁ ⇒ f ∘ (π₂ ,→ μ) → f ⇒ ∂
    ∂-is-determined-by-a-triangle f triangle =
      unwhisker-equivalence f ∂ (π₂ ,→ μ)
        invertibilty-as-automorphism-of-the-product
        (triangle ⁻¹⇒ •⇒ ∂-triangle)


    two-solutions-are-equal :
      ∀ {a b : X} (x y : X)
      → (x ‣ a) ≈ b → (y ‣ a) ≈ b
      → x ≈ y
    two-solutions-are-equal {a} {b} x y γ η =
      let
        c = contraction (uniqueness-of-left-translations a b)
      in ∑π₁ ⁎ (c (x , γ) ⁻¹ • c (y , η))

    left-difference-is-a-solution :
      ∀ (a b : X)
      → (b ‣ a ⁻) ‣ a ≈ b
    left-difference-is-a-solution a b = left-inverses-are-also-right-inverses (λ x → x ‣ a)
                                          (left-inverse (left-invertible a))
                                          (right-inverse (left-invertible a)) (unit (left-invertible a))
                                          (counit (left-invertible a)) b

    left-difference-is-unique :
      ∀ (a b : X)
      → (∑ λ (x : X) → (x ‣ a ⁻) ≈ b) is-contractible
    left-difference-is-unique a b =  types-equivalent-to-contractibles-are-contractible
                                       (fiber-as-sum ⁻¹≃)
                                       (contractible-fibers-characterize-equivalences.to-fiber-condition
                                         (left-invert a) (left-inverting-is-an-equivalence a) b)


    left-difference-is-unique′ :
      ∀ (a b : X)
      → (∑ λ (x : X) → b ≈ (x ‣ a ⁻)) is-contractible
    left-difference-is-unique′ a b = types-equivalent-to-contractibles-are-contractible
                                       (the-equivalence-of-sums-given-by (λ x γ → γ ⁻¹)
                                          being-fiberwise-an-equivalence-by (λ x → inversion-is-an-equivalence.proof))
                                       (left-difference-is-unique a b)


  

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


    as-non-associative-group : left-invertible-structure-on (Ω BG e)
    as-non-associative-group = record { e = refl;
                          μ = λ {(γ , η) → γ • η};
                          left-neutral = refl-is-left-neutral;
                          right-neutral = refl-is-right-neutral ⁻¹⇒;
                          left-invertible = right-composing-is-an-equivalence} 


    

  {-
    for all groups G and φ:D→G, we have a pullback square:

    G×D ─π₂─→ D
     |        |
     |        φ
     |        |
     ↓        ↓
    G×G ─∂──→ G

    (look at the code below for the definition of all maps)
  -}

  module mayer-vietoris-lemma {G D : U₀} (structure : left-invertible-structure-on G) (φ : D → G) where
    open left-invertible-structure-on_ structure


    {- get a starting pullback square where the pullback is written as
        an iterated sigma-type. this will ease manipulation.

 ∑∑∑φ(d)≈∂(g,h) ─π₂─→ D
       |              |
       |              φ
       |              |
       ↓              ↓
      G×G ─────∂────→ G

    -}
    square1 = square-with-pullback-as-iterated-∑ φ ∂

    {-
      ∑(d : D) ∑((g,h):G×G) φ(d)≈∂(g,h) ≃ ∑(d : D) ∑(g : G) ∑(h : G)  φ(d)≈∂(g,h) 
    -}

    uncurry-G×G : (∑ λ d → ∑ λ g → ∑ λ h → φ(d) ≈ h ‣ g ⁻) → ∑ (λ d → ∑ λ {(g , h) → φ(d) ≈ h ‣ g ⁻})
    uncurry-G×G (d , (g , (h , γ))) = (d , ((g , h) , γ))
 
    uncurrying-G×G-is-an-equivalence : uncurry-G×G is-an-equivalence
    uncurrying-G×G-is-an-equivalence =
      the-map-of-sums-given-by
        (λ d → iterated-sums-over-independent-bases.uncurry
               G G (λ g h → φ(d) ≈ h ‣ g ⁻))
       is-an-equivalence-since-it-is-fiberwise-an-equivalence-by
         (λ d → iterated-sums-over-independent-bases.uncurrying-is-an-equivalence
               G G (λ g h → φ(d) ≈ h ‣ g ⁻))
               
    square2 = substitute-equivalent-cone
                ∑π₁ (λ {(d , (g , (h , γ))) → g , h})
                uncurry-G×G uncurrying-G×G-is-an-equivalence
                (λ {(d , (g , (h , γ))) → refl}) (λ {(d , (g , (h , γ))) → refl})
                square1

    {- the inner most ∑ ist contractible
       this way of proving it, was written by mike shulman somewhere on the nlab
       
       ∑(d : D) ∑(g : G) ∑(h : G) φ(d)≈∂(g,h) ≃ ∑(x : D × G) 1 ≃ D × G

       first, curry the outer two (square3):
       
       ∑(d : D) ∑(g : G) ∑(h : G) φ(d)≈∂(g,h) ≃ ∑(x : D × G) ∑(h : G) φ(π₁(x))≈∂(π₂(x),h) 
 
       second, use contractibility of the innermost sum:

       ∑(x : D × G) ∑(h : G) φ(π₁(x))≈∂(π₂(x),h) ≃ D × G
    -}


    curry-D×G :
        (∑ λ (x : D × G) → ∑ λ h → φ(π₁ x) ≈ h ‣ (π₂ x) ⁻)
      → ∑ λ d → ∑ λ g → ∑ λ h → φ(d) ≈ h ‣ g ⁻
    curry-D×G = iterated-sums-over-independent-bases.curry D G _

    square3 = substitute-equivalent-cone
                (λ {((d , _) , _) → d}) (λ {((_ , g) , (h , _)) → (g , h)})
                curry-D×G (iterated-sums-over-independent-bases.currying-is-an-equivalence D G _)
                (λ _ → refl) (λ _ → refl)
                square2


    inner-sum-is-contractible :
      ∀ (x : D × G)
      → (∑ λ h → φ(π₁ x) ≈ h ‣ (π₂ x) ⁻) is-contractible
    inner-sum-is-contractible (d , g) = left-difference-is-unique′ g (φ d)
    
    equivalence-to-product :
        D × G
      → ∑ λ (x : D × G) → ∑ λ h → φ(π₁ x) ≈ h ‣ (π₂ x) ⁻
    equivalence-to-product = sums-over-contractibles.section
                                   (∑ λ (d : D) → G) _ (λ {(d , g) → inner-sum-is-contractible (d , g)}) 

    square4 : pullback-square-with-right φ
                bottom ∂
                top π₁
                left (λ {(d , g) → (g , (φ d) ‣ g)})
    square4 = substitute-equivalent-cone
                π₁ (λ {(d , g) → (g , (φ d) ‣ g)})
                equivalence-to-product
                (sums-over-contractibles.section-is-an-equivalence (D × G) _
                                        inner-sum-is-contractible)
                (λ _ → refl) (λ {(d , g) → refl})
                square3

    {-
             D × G ────π₁───→ D
               | ⌟            |
               |              |
    (d,g)↦(g,μ(φ(d),g))       φ
               |              |
               ↓              ↓
             G × G ───∂─────→ G 
    -}


    result-as-square = square4
