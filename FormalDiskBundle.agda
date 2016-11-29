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


  _is-infinitesimally-close-to_ :
    ∀ {A : U₀} (a a′ : A)
    → U₀
  a is-infinitesimally-close-to a′ = ℑ-unit a ≈ ℑ-unit a′

  formal-disk-at_ :
    ∀ {A : U₀} (a₀ : A)
    → (A → U₀)
  formal-disk-at a₀ = λ a → a is-infinitesimally-close-to a₀

  T∞′ :
    ∀ (A : U₀) → (A → U₀)
  T∞′ A a = ∑ (formal-disk-at a)

  formal-disk-bundle : (X : U₀) → U₀
  formal-disk-bundle X = pullback (ℑ-unit-at X) (ℑ-unit-at X)

  T∞ : (X : U₀) → U₀
  T∞ X = formal-disk-bundle X

  p-of-T∞ : (X : U₀) → (T∞ X) → X
  p-of-T∞ X = p₂-of-pullback (ℑ-unit-at X) (ℑ-unit-at X)

  formal-disk-bundle-as-pullback-square :
    ∀ (X : U₀) → pullback-square-with-right ℑ-unit bottom ℑ-unit top p₁ left p₂
  formal-disk-bundle-as-pullback-square X = complete-to-pullback-square (ℑ-unit-at X) (ℑ-unit-at X)



  module triviality-of-the-formel-disk-bundle-over-∞-groups (BG : U₀) (e : BG) where
    G = Ω BG e

    ℑG = ℑ G
    ℑG′ = Ω (ℑ BG) (ℑ-unit e)

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

  -- Step 2:
  --  ℑG ---→ ∗
  --   |  ⌟   |
  --   Δ      |
  --   ↓      ↓
  --ℑG × ℑG → ℑG′
  --

  -- Step 2a:
  --  ℑG′ ----→ ∗
  --   |  ⌟     |
  --   Δ        |
  --   ↓        ↓
  --ℑG′ × ℑG′ → ℑG′
  --
    


    constant-refl-e : One → ℑG′
    constant-refl-e x = refl

    ν : One × ℑG′ → One
    ν = lemma-on-pullbacks-of-Δ.ν (ℑ BG) (ℑ-unit e) One constant-refl-e 
    θ = lemma-on-pullbacks-of-Δ.θ (ℑ BG) (ℑ-unit e) One constant-refl-e 

    constant-∗ : ℑG′ → One
    constant-∗ x = ∗

    step2a′ : pullback-square-with-right constant-refl-e 
              bottom ℑGΔ′
              top ν
              left θ
    step2a′ = lemma-on-pullbacks-of-Δ.as-pullback-square 
              (ℑ BG) (ℑ-unit e) One constant-refl-e

    step2a : pullback-square-with-right constant-refl-e
              bottom ℑGΔ′
              top constant-∗
              left Δ
    step2a = substitute-equivalent-cone constant-∗ Δ (λ g → ∗ , g)
               (has-left-inverse (λ { (∗ , g) → g }) by (λ _ → refl)
                and-right-inverse (λ { (∗ , g) → g }) by (λ { (∗ , g) → refl }))
               (λ _ → refl) (λ _ → refl) step2a′




  {-
   Step 2b:
       ℑG ----≃---- ℑG′
        |            |
        Δ            Δ 
        ↓            ↓
     ℑG × ℑG -≃- ℑG′ × ℑG′
  -}

    ψ : ℑG → ℑG′
    ψ = ℑ-induction (λ γ → Ω-of-ℑ-is-coreduced BG e) (λ γ → ℑ-unit ⁎ γ)

    ψ-of-refl : ψ (ℑ-unit refl) ≈ ℑ-unit ⁎ refl
    ψ-of-refl = ℑ-compute-induction (λ γ → Ω-of-ℑ-is-coreduced BG e) (λ γ → ℑ-unit ⁎ γ) refl

    ψ-as-equivalence : ℑG ≃ ℑG′
    ψ-as-equivalence = ψ is-an-equivalence-because (ℑ-commutes-with-Ω BG e)
    
    ψ⁻¹l = left-inverse-of-the-equivalence ψ-as-equivalence
    ψ⁻¹l∘ψ⇒id = unit-of-the-equivalence ψ-as-equivalence
    ψ⁻¹r = right-inverse-of-the-equivalence ψ-as-equivalence
    id⇒ψ∘ψ⁻¹r = counit-of-the-equivalence ψ-as-equivalence

    step2b : pullback-square-with-right Δ bottom (ψ ×→ ψ) top ψ left Δ
    step2b = pullback-square-from-equivalence-of-maps Δ Δ ψ-as-equivalence 
             ((ψ ×→ ψ) is-an-equivalence-because 
               (has-left-inverse ψ⁻¹l ×→ ψ⁻¹l by (λ {(_ , _) → ×-create-equality (ψ⁻¹l∘ψ⇒id _) (ψ⁻¹l∘ψ⇒id _)}) 
                and-right-inverse ψ⁻¹r ×→ ψ⁻¹r by (λ { (_ , _) → ×-create-equality (id⇒ψ∘ψ⁻¹r _) (id⇒ψ∘ψ⁻¹r _) }))) 
             (λ _ → refl)

    {- Step 2c:

       ℑG ----→ ∗
        |  ⌟    |
        Δ       |
        ↓       ↓
     ℑG × ℑG → ℑG′

    -}

    step2c : pullback-square-with-right constant-refl-e bottom ℑGΔ′ ∘ (ψ ×→ ψ) top (λ _ → ∗) left Δ
    step2c = pasting-of-pullback-squares step2b step2a

    {-
    Step 3 (combine step 1 and 2c):

       T∞ G  -→ ℑG           ℑG ----→ ∗      T∞ G ---→ ∗
        |  ⌟    |             |  ⌟    |        |  ⌟    |
        |       Δ      and    Δ       |   ⇒    |       |
        ↓       ↓             ↓       ↓        ↓       ↓
     G × G → ℑG × ℑG       ℑG × ℑG → ℑG′     G × G --→ ℑG′
    
    -}

    step3′ : pullback-square-with-right constant-refl-e 
              bottom ℑGΔ′ ∘ (ψ ×→ ψ) ∘ (ℑ-unit-at G ×→ ℑ-unit-at G)
              top (λ _ → ∗) 
              left forget-path 
    step3′ = pasting-of-pullback-squares step1 step2c

    describe-ψ∘ℑ-unit : ψ ∘ ℑ-unit-at (Ω BG e) ⇒ (λ γ → ℑ-unit ⁎ γ)
    describe-ψ∘ℑ-unit γ = ℑ-compute-induction (λ γ₁ → Ω-of-ℑ-is-coreduced BG e)
                            (λ γ₁ → ℑ-unit ⁎ γ₁) γ

    coreduce-and-divide : G × G → ℑG′
    coreduce-and-divide (g , h) = ℑ-unit-at BG ⁎ g • ℑ-unit-at BG ⁎ h ⁻¹

    describe-the-bottom-map : ℑGΔ′ ∘ (ψ ×→ ψ) ∘ (ℑ-unit-at G ×→ ℑ-unit-at G) ⇒ coreduce-and-divide
    describe-the-bottom-map (g , h) = 
      ℑGΔ′ ⁎ (×-create-equality (describe-ψ∘ℑ-unit g) (describe-ψ∘ℑ-unit h))

    step3 : pullback-square-with-right constant-refl-e 
              bottom coreduce-and-divide
              top (λ _ → ∗) 
              left forget-path 
    step3 = (substitute-homotopic-bottom-map step3′
               coreduce-and-divide (describe-the-bottom-map ⁻¹⇒))

    {-
  
    Step 4: Factor the square from step 3
            and get rid of the ℑG′
             T∞ G --→ De -→ ∗
            ⌟ |       | ⌟   |
 forget-path  |       |     |
              ↓       ↓     ↓
            G × G --→ G -→ ℑG

        -divide-and-coreduce→
    
    -}

    De = D G (refl {a = e})

    ∂G : G × G → G
    ∂G (g , h) = g • h ⁻¹ 

    remove-ℑG′ =
             (pullback-square-from-equivalence-of-maps 
                (λ (x : One) → ℑ-unit (refl {a = e})) 
                (λ (x : One) → ℑ-unit ⁎ (refl {a = e})) 
                id-as-equivalence 
                (ψ-as-equivalence ⁻¹≃) (λ ∗ → ℑ-unit refl 
                                             ≈⟨ ψ⁻¹l∘ψ⇒id (ℑ-unit refl) ⁻¹ ⟩ 
                                              ψ⁻¹l (ψ (ℑ-unit refl))
                                             ≈⟨ ψ⁻¹l ⁎ ψ-of-refl ⟩
                                              ψ⁻¹l refl
                                             ≈∎))

    
    step4 : pullback-square-with-right (λ _ → ℑ-unit refl)
              bottom ψ⁻¹l ∘ (λ g → ℑ-unit ⁎ g) ∘ ∂G
              top (λ _ → ∗)
              left forget-path
    step4 = pasting-of-pullback-squares 
             (substitute-homotopic-bottom-map step3
              ((λ g → ℑ-unit ⁎ g) ∘ ∂G) (λ {(g , h) →
                ℑ-unit ⁎ (g • h ⁻¹) 
               ≈⟨ application-commutes-with-concatenation ℑ-unit g (h ⁻¹) ⟩
                ℑ-unit ⁎ g • ℑ-unit ⁎ (h ⁻¹) 
               ≈⟨ (λ ξ → ℑ-unit ⁎ g • ξ) ⁎ application-commutes-with-inversion ℑ-unit h ⟩ 
                ℑ-unit ⁎ g • ℑ-unit ⁎ h ⁻¹ ≈∎}))
             remove-ℑG′

    {-
  
    the right square
      
     De -→ ∗
     | ⌟   |
     |     |
     ↓     ↓
     G -→ ℑG
    
    -}

    φ : De → G
    φ = p₂

    the-De-square : pullback-square-with-right (λ _ → ℑ-unit refl)
                      bottom ℑ-unit
                      top p₁
                      left φ
    the-De-square = complete-to-pullback-square (λ ∗ → (ℑ-unit-at G) (refl {a = e})) (ℑ-unit-at G)
    
    ψ-commutes-with-ℑ-units : 
      ψ ∘ ℑ-unit ⇒ (λ g → ℑ-unit ⁎ g)
    ψ-commutes-with-ℑ-units g = ℑ-compute-induction (λ γ₁ → Ω-of-ℑ-is-coreduced BG e)
                                                     (λ γ₁ → ℑ-unit ⁎ γ₁) g

    the-De-square′ : pullback-square-with-right (λ _ → ℑ-unit refl)
                      bottom ψ⁻¹l ∘ (λ g → ℑ-unit ⁎ g)
                      top p₁
                      left φ
    the-De-square′ = substitute-homotopic-bottom-map the-De-square (ψ⁻¹l ∘ (λ g → ℑ-unit ⁎ g)) 
                      (λ x → (ψ⁻¹l ∘ (λ g → ℑ-unit ⁎ g)) x
                             ≈⟨ ψ⁻¹l ⁎ ψ-commutes-with-ℑ-units x ⁻¹ ⟩
                              (ψ⁻¹l ∘ ψ ∘ ℑ-unit) x
                             ≈⟨ ψ⁻¹l∘ψ⇒id (ℑ-unit x) ⟩
                              ℑ-unit x
                             ≈∎) 

    {- 
    Step 5: Conclude, that the left square
     T∞ G ---→ De
      | ⌟      |
      |        φ 
      ↓        ↓ 
    G × G -∂G→ G

    is a pullback
    -}

    right-square = the-De-square′

    step5 : pullback-square-with-right φ
              bottom ∂G
              top _
              left forget-path
    step5 = cancel-the-right-pullback-square
              right-square
            from
              step4 

    {- Step 6a: Same cospan 'different' pullback

     De × G --> De
       | ⌟      |
       |        φ
       ↓        ↓
     G × G ---> G
    
    -}

    step6a′ : pullback-square-with-right φ 
                bottom (∞-group-Δ BG e) 
                top lemma-on-pullbacks-of-Δ.ν BG e De φ 
                left lemma-on-pullbacks-of-Δ.θ BG e De φ
    step6a′ = lemma-on-pullbacks-of-Δ.as-pullback-square BG e De φ 

    step6a : pullback-square-with-right φ 
               bottom ∂G
               top lemma-on-pullbacks-of-Δ.ν BG e De φ 
               left lemma-on-pullbacks-of-Δ.θ BG e De φ
    step6a = substitute-homotopic-bottom-map step6a′ ∂G (λ {(g , h) → refl})

    -- Step6b: deduce equivalence ∎
    step6b : De × G ≃ T∞ G
    step6b = deduce-equivalence-of-vertices step6a step5

    step6b′ : T∞ G ≃ De × G 
    step6b′ = deduce-equivalence-of-vertices step5 step6a

    as-product-square′ : 
      pullback-square-with-right (λ (d : De) → ∗)
        bottom (λ (g : G) → ∗)
        top _
        left _ 
    as-product-square′ = 
      step6a and step5 pull-back-the-same-cospan-so-the-first-may-be-replaced-by-the-second-in-the-square (product-square De G)

    χ′ : T∞ G → G
    χ′ (g₁ and g₂ are-in-the-same-fiber-by γ) = g₂

    χ′⇒π₂∘step6b′ : (lemma-on-pullbacks-of-Δ.θ BG e De φ) ∘ (underlying-map-of step6b′) ⇒ forget-path
    χ′⇒π₂∘step6b′ = 
      deduced-equivalence-factors-the-left-map step5 step6a

    χ′⇒π₂∘step6b : χ′ ⇒ π₂ ∘ (underlying-map-of step6b′)
    χ′⇒π₂∘step6b (g₁ and g₂ are-in-the-same-fiber-by γ) = π₂ ⁎ (χ′⇒π₂∘step6b′ (g₁ and g₂ are-in-the-same-fiber-by γ))

    χ : T∞ G → G
    χ (g₁ and g₂ are-in-the-same-fiber-by γ) = g₁


    as-product-square : 
      pullback-square-with-right (λ (d : De) → ∗)
        bottom (λ (g : G) → ∗)
        top _
        left χ′
    as-product-square = 
      substitute-homotopic-left-map as-product-square′ χ′ (χ′⇒π₂∘step6b)
