{-# OPTIONS --without-K #-}

module PullbackSquare where 
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Fiber 
  open import Equivalences
  open import CommonEquivalences
  open import HalfAdjointEquivalences
  open import FunctionExtensionality
  open import Pullback
  open import PullbackPasting
  

  {-

     pullback-square formalism

     Z -z₁→ A
     |      |
     z₂     f
     |      |
     v      v
     B -g-→ C

  -}

  record pullback-square {i} {Z A B C : U i} (f : A → C)  (g : B → C) 
                                      (z₁ : Z → A) (z₂ : Z → B)  : U i where
    constructor the-square-commuting-by_and-inducing-an-equivalence-by_
    field
      γ : f ∘ z₁ ⇒ g ∘ z₂
      proof : (induced-map-to-pullback {_} {_} {_} {_} {_} {f} {g}  z₁ z₂ γ) is-an-equivalence

  record is-a-pullback-square {i} {Z A B C : U i} 
    (f : A → C)  (g : B → C) 
    (z₁ : Z → A) (z₂ : Z → B) (γ : f ∘ z₁ ⇒ g ∘ z₂) : U i where
    constructor the-induced-map-is-an-equivalence-by_
    field 
      proof : (induced-map-to-pullback {_} {_} {_} {_} {_} {f} {g}  z₁ z₂ γ) is-an-equivalence

  -- Language
  pullback-square-with-right_bottom_top_left_ :
    ∀ {Z A B C : U₀}
      (f : A → C)  (g : B → C) 
      (z₁ : Z → A) (z₂ : Z → B)
      → U₀
  pullback-square-with-right f bottom g top z₁ left z₂ =
    pullback-square f g z₁ z₂

  the-square-with-right_bottom_top_left_commuting-by_is-a-pullback-square :
    ∀ {Z A B C : U₀}
      (f : A → C)  (g : B → C) 
      (z₁ : Z → A) (z₂ : Z → B)
      → (γ : f ∘ z₁ ⇒ g ∘ z₂)
      → U₀
  the-square-with-right f bottom g top z₁ left z₂ commuting-by γ is-a-pullback-square =
    is-a-pullback-square f g z₁ z₂ γ
    

  -- projections
  underlying-2-cell : 
    ∀ {Z A B C : U₀}
      {f : A → C}  {g : B → C}
      {z₁ : Z → A} {z₂ : Z → B}
      → pullback-square f g z₁ z₂
      → f ∘ z₁ ∼ g ∘ z₂
  underlying-2-cell
    (the-square-commuting-by γ and-inducing-an-equivalence-by _)  = γ

  the-induced-map-in_is-an-equivalence : 
    ∀ {Z A B C : U₀}
      {f : A → C}  {g : B → C}
      {z₁ : Z → A} {z₂ : Z → B}
      → (□ : pullback-square f g z₁ z₂)
      → induced-map-to-pullback z₁ z₂ (underlying-2-cell □) is-an-equivalence
  the-induced-map-in (the-square-commuting-by _ and-inducing-an-equivalence-by proof) is-an-equivalence = 
    proof

  upper-left-vertex-of :
    ∀ {Z A B C : U₀}
      {f : A → C}  {g : B → C}
      {z₁ : Z → A} {z₂ : Z → B}
    → pullback-square f g z₁ z₂
    → U₀
  upper-left-vertex-of {Z} {_} {_} {_} {_} {_} {_} {_} _ = Z

  lower-left-vertex-of :
    ∀ {Z A B C : U₀}
      {f : A → C}  {g : B → C}
      {z₁ : Z → A} {z₂ : Z → B}
    → pullback-square f g z₁ z₂
    → U₀
  lower-left-vertex-of {_} {_} {B} {_} {_} {_} {_} {_} _ = B

  lower-right-vertex-of :
    ∀ {Z A B C : U₀}
      {f : A → C}  {g : B → C}
      {z₁ : Z → A} {z₂ : Z → B}
    → pullback-square f g z₁ z₂
    → U₀
  lower-right-vertex-of {_} {_} {_} {C} {_} {_} {_} {_} _ = C

  upper-right-vertex-of :
    ∀ {Z A B C : U₀}
      {f : A → C}  {g : B → C}
      {z₁ : Z → A} {z₂ : Z → B}
    → pullback-square f g z₁ z₂
    → U₀
  upper-right-vertex-of {_} {A} {_} {_} {_} {_} {_} {_} _ = A

  left-map-of :
    ∀ {Z A B C : U₀}
      {f : A → C}  {g : B → C}
      {z₁ : Z → A} {z₂ : Z → B}
    → pullback-square f g z₁ z₂
    → (Z → B)
  left-map-of {_} {_} {_} {_} {_} {_} {_} {z₂} _ = z₂

  right-map-of :
    ∀ {Z A B C : U₀}
      {f : A → C}  {g : B → C}
      {z₁ : Z → A} {z₂ : Z → B}
    → pullback-square f g z₁ z₂
    → (A → C)
  right-map-of {_} {_} {_} {_} {f} {_} {_} {_} _ = f

  bottom-map-of :
    ∀ {Z A B C : U₀}
      {f : A → C}  {g : B → C}
      {z₁ : Z → A} {z₂ : Z → B}
    → pullback-square f g z₁ z₂
    → (B → C)
  bottom-map-of {_} {_} {_} {_} {_} {g} {_} {_} _ = g

  top-map-of :
    ∀ {Z A B C : U₀}
      {f : A → C}  {g : B → C}
      {z₁ : Z → A} {z₂ : Z → B}
    → pullback-square f g z₁ z₂
    → (Z → A)
  top-map-of {_} {_} {_} {_} {_} {_} {z₁} {_} _ = z₁

  -- induced maps to abstract pullbacks
  induced-map-to-pullback-vertex :
    ∀ {W Z A B C : U₀}
      {f : A → C}  {g : B → C}
      {z₁ : Z → A} {z₂ : Z → B}
      → (□ : pullback-square f g z₁ z₂)
      → (w₁ : W → A) → (w₂ : W → B) → (η : f ∘ w₁ ⇒ g ∘ w₂)
      → (W → Z)
  induced-map-to-pullback-vertex {W} {_} {_} {_} {_} {f} {g} {_} {_}  □ w₁ w₂ η =
    let 
      φ : W → pullback f g 
      φ = induced-map-to-pullback w₁ w₂ η
      
      ψ⁻¹ = _is-an-equivalence.left-inverse (the-induced-map-in □ is-an-equivalence)
    in ψ⁻¹ ∘ φ

  deduce-equivalence-of-vertices :
    ∀ {W Z A B C : U₀}
      {f : A → C}  {g : B → C}
      {z₁ : Z → A} {z₂ : Z → B}
      {w₁ : W → A} {w₂ : W → B}
      → (□₁ : pullback-square f g z₁ z₂)
      → (□₂ : pullback-square f g w₁ w₂)
      → Z ≃ W
  deduce-equivalence-of-vertices {W} {Z} {_} {_} {_} {f} {g} {z₁} {z₂} {w₁} {w₂}
    (the-square-commuting-by γ and-inducing-an-equivalence-by x) 
    (the-square-commuting-by γ₁ and-inducing-an-equivalence-by x₁) =
    let
      φ : W ≃ pullback f g
      φ = (induced-map-to-pullback w₁ w₂ γ₁) is-an-equivalence-because x₁
      ψ : Z ≃ pullback f g
      ψ = (induced-map-to-pullback z₁ z₂ γ) is-an-equivalence-because x
    in φ ⁻¹≃ ∘≃ ψ  

  -- get factorization for this equivalence
  deduced-equivalence-factors-the-left-map : 
    ∀ {W Z A B C : U₀}
      {f : A → C}  {g : B → C}
      {z₁ : Z → A} {z₂ : Z → B}
      {w₁ : W → A} {w₂ : W → B}
      → (□₁ : pullback-square f g z₁ z₂)
      → (□₂ : pullback-square f g w₁ w₂)
      → w₂ ∘ (underlying-map-of (deduce-equivalence-of-vertices □₁ □₂)) ⇒ z₂ 
  deduced-equivalence-factors-the-left-map {W} {Z} {_} {_} {_} {f} {g} {z₁} {z₂} {w₁} {w₂} 
    (the-square-commuting-by γ and-inducing-an-equivalence-by x) 
    (the-square-commuting-by γ₁ and-inducing-an-equivalence-by (has-left-inverse φ⁻¹l by unit and-right-inverse φ⁻¹r by counit)) =
    let
      ψ : Z → pullback f g
      ψ = (induced-map-to-pullback z₁ z₂ γ) 
      φ : W → pullback f g
      φ = (induced-map-to-pullback w₁ w₂ γ₁) 
      w₂∘φ⁻¹l⇒p₂ : w₂ ∘ φ⁻¹l ⇒ p₂ 
      w₂∘φ⁻¹l⇒p₂ z = 
                w₂ (φ⁻¹l z)
              ≈⟨ (w₂ ∘ φ⁻¹l) ⁎ counit z • w₂ ⁎ unit (φ⁻¹r z) ⟩ 
                w₂ (φ⁻¹r z)
              ≈⟨ refl ⟩
                p₂ (φ (φ⁻¹r z))
              ≈⟨ p₂ ⁎ counit z ⁻¹ ⟩
                p₂ z ≈∎
      χ : Z → W
      χ = underlying-map-of 
          (deduce-equivalence-of-vertices 
            (the-square-commuting-by γ and-inducing-an-equivalence-by x) 
            (the-square-commuting-by γ₁ and-inducing-an-equivalence-by (has-left-inverse φ⁻¹l by unit and-right-inverse φ⁻¹r by counit)))
    in λ z → w₂ (χ z) 
           ≈⟨ w₂∘φ⁻¹l⇒p₂ (ψ z) ⟩ 
             z₂ z ≈∎

  equality-of-squares-preserve-the-pullback-property : 
    ∀ {Z A B C : U₀} 
      {f : A → C}  {g : B → C}
      {z₁ : Z → A} {z₂ : Z → B}
     → (□ : pullback-square f g z₁ z₂)
     → (η : f ∘ z₁ ⇒ g ∘ z₂) 
     → ((z : Z) → η z ≈ underlying-2-cell □ z)
     → pullback-square f g z₁ z₂
  equality-of-squares-preserve-the-pullback-property
    {Z} {_} {_} {_} {f} {g} {z₁} {z₂} □ η H =
      let
        -- show: the map induced by η (=:φ) is homotopic 
        --   to the induced map in the given square (=:ψ)
        --   which is known to be an equivalence

        γ = (underlying-2-cell □)
        ψ : Z → pullback f g
        ψ = induced-map-to-pullback z₁ z₂ γ

        φ : Z → pullback f g
        φ = induced-map-to-pullback z₁ z₂ η
        
        φ⇒ψ : φ ⇒ ψ
        φ⇒ψ = uniqueness-of-induced-maps z₁ z₂ γ φ (λ _ → refl) (λ _ → refl) (λ z → refl-is-right-neutral (η z) ⁻¹ • H z)

      in the-square-commuting-by η and-inducing-an-equivalence-by 
         (the-map φ is-an-equivalence-since-it-is-homotopic-to ψ by φ⇒ψ
          which-is-an-equivalence-by the-induced-map-in □ is-an-equivalence)




  -- given any cospan, we may construct a pullback square:
  complete-to-pullback-square :
    ∀ {A B C : U₀} (f : A → C) (g : B → C)
    → pullback-square f g (p₁-of-pullback f g) (p₂-of-pullback f g)
  complete-to-pullback-square f g = 
    let step1 : id left-inverse-of induced-map-to-pullback (p₁-of-pullback _ _) (p₂-of-pullback _ _) p-homotopy
        step1  = λ {(a and b are-in-the-same-fiber-by γ) → refl}

        step2 : id right-inverse-of induced-map-to-pullback 
                 (p₁-of-pullback _ _) (p₂-of-pullback _ _) p-homotopy
        step2 = λ {(a and b are-in-the-same-fiber-by γ) → refl}
    in the-square-commuting-by p-homotopy and-inducing-an-equivalence-by
      (has-left-inverse id by step1 and-right-inverse id by step2)


 
  square-with-pullback-as-iterated-∑ :
    ∀ {A B C : U₀} (f : A → C) (g : B → C)
    → pullback-square f g ∑π₁ (λ x → ∑π₁ (∑π₂ x))
  square-with-pullback-as-iterated-∑ {A} {B} {C} f g =
    let
      as-sum = ∑ (λ (a : A) → ∑ (λ (b : B) → f(a) ≈ g(b)))

      ψ : as-sum → pullback f g
      ψ = λ {(a , (b , γ)) → a and b are-in-the-same-fiber-by γ}

      ψ⁻¹ : pullback f g → as-sum 
      ψ⁻¹ = λ {(a and b are-in-the-same-fiber-by γ) → (a , (b , γ))}
      
    in the-square-commuting-by (λ {(a , (b , γ)) → γ})
       and-inducing-an-equivalence-by
       (the-map _ is-an-equivalence-since-it-is-homotopic-to ψ by (λ _ → refl)
        which-is-an-equivalence-by
         (has-left-inverse ψ⁻¹ by (λ _ → refl) and-right-inverse ψ⁻¹ by (λ _ → refl)))
    
  {- for all products A × B there is a pullback square

    A×B ─π₁→ A
     | ⌟     |
     π₂      |
     ↓       ↓
     B ────→ C
  -}
  product-square : 
    ∀ (A B : U₀)
    → pullback-square-with-right (λ (a : A) → ∗)
        bottom (λ (b : B) → ∗)
        top π₁
        left π₂
  product-square A B = 
    the-square-commuting-by (λ x → refl) 
    and-inducing-an-equivalence-by
      products-are-special-pullbacks.induced-map-is-an-equivalence A B

  pullback-square-from-identity-of-morphisms : 
    ∀ {A B : U₀}
    → (f : A → B)
    → pullback-square-with-right f bottom id top id left f
  pullback-square-from-identity-of-morphisms f = 
    the-square-commuting-by (λ z → refl) and-inducing-an-equivalence-by 
      (the-map (induced-map-to-pullback id f (λ a → refl))
       is-an-equivalence-since-it-is-homotopic-to
       (domain-to-id-pullback′ _ _ f) by (λ a → refl) 
       which-is-an-equivalence-by 
        (the-inverse-of (id-pullback-to-domain′ _ _ f)
         which-is-an-equivalence-by (id-pullback-is-domain′ _ _ f)
         is-again-an-equivalence))

  {- fibers are pullbacks

    fiber-of f at b ─ι→ A
                | ⌟     |
                |       f
                ↓       ↓
                1 ────→ B
  -}

  fiber-square-for_at_ : 
    ∀ {A B : U₀} (f : A → B) (b : B)
    → pullback-square-with-right f
        bottom (λ _ → b)
        top ι-fiber
        left (λ (_ : fiber-of f at b) → ∗)
  fiber-square-for f at b =
    let inverse : pullback f (λ _ → b) → fiber-of f at b
        inverse = λ {(a and ∗ are-in-the-same-fiber-by η) → a is-in-the-fiber-by η}
    in the-square-commuting-by (λ {(a is-in-the-fiber-by γ) → γ}) 
       and-inducing-an-equivalence-by
        (has-left-inverse inverse by (λ {(a is-in-the-fiber-by η) → refl})
         and-right-inverse inverse by (λ {(a and ∗ are-in-the-same-fiber-by η) → refl}))

  -- switching the maps in the cospan
  rotate-cospan : 
    ∀ {Z A B C : U₀} 
    {f : A → C}  {g : B → C}
    {z₁ : Z → A} {z₂ : Z → B}
    → pullback-square f g z₁ z₂
    → pullback-square g f z₂ z₁
  rotate-cospan {_} {_} {_} {_} {f} {g} {z₁} {z₂} 
    (the-square-commuting-by γ and-inducing-an-equivalence-by proof-of-equivalence) 
    = the-square-commuting-by (γ ⁻¹∼) 
      and-inducing-an-equivalence-by 
      switching-the-maps-factors-cones-by-an-equivalence.switching-preserves-equivalences
      f g _ z₁ z₂ γ proof-of-equivalence


  substitute-homotopic-right-map : 
    ∀ {Z A B C : U₀} 
     {f : A → C}  {g : B → C}
     {z₁ : Z → A} {z₂ : Z → B}
    → pullback-square f g z₁ z₂
    → (f′ : A → C) → f′ ∼ f
    → pullback-square f′ g z₁ z₂
  substitute-homotopic-right-map {Z} {A} {B} {C} {f} {g} {z₁} {z₂} 
    (the-square-commuting-by γ and-inducing-an-equivalence-by proof-of-equivalency) f′ H =
    let
      new-homotopy : f′ ∘ z₁ ∼ g ∘ z₂
      new-homotopy z = H (z₁ z) • γ z

      induced-map-between-canonicals : pullback f g → pullback f′ g
      induced-map-between-canonicals = λ {(a and b are-in-the-same-fiber-by η) → a and b are-in-the-same-fiber-by H a • η}

      old-induced-map : Z → pullback f g
      old-induced-map = induced-map-to-pullback z₁ z₂ γ

      induced-map : Z → pullback f′ g
      induced-map = induced-map-to-pullback z₁ z₂ new-homotopy

      step1 : induced-map-between-canonicals ∘ old-induced-map ∼ induced-map
      step1 z = refl

      induced-map-is-an-equivalence :
        induced-map is-an-equivalence
      induced-map-is-an-equivalence = 
        the-map induced-map is-an-equivalence-since-it-is-homotopic-to
        (induced-map-between-canonicals ∘ old-induced-map) by step1
        which-is-an-equivalence-by 
          (the-composition-of-equivalences-is-an-equivalence old-induced-map
            induced-map-between-canonicals proof-of-equivalency 
             (the-map induced-map-between-canonicals
               is-an-equivalence-since-it-is-homotopic-to
               homotopy-invariance.e⁻¹ f f′ g H by (λ { (_ and _ are-in-the-same-fiber-by _) → refl }) which-is-an-equivalence-by
               homotopy-invariance.e⁻¹-is-an-equivalence f f′ g H))

    in the-square-commuting-by new-homotopy 
       and-inducing-an-equivalence-by induced-map-is-an-equivalence

  substitute-homotopic-bottom-map : 
    ∀ {Z A B C : U₀} 
     {f : A → C}  {g : B → C}
     {z₁ : Z → A} {z₂ : Z → B}
    → pullback-square f g z₁ z₂
    → (g′ : B → C) → g′ ∼ g
    → pullback-square f g′ z₁ z₂
  substitute-homotopic-bottom-map {Z} {A} {B} {C} {f} {g} {z₁} {z₂} 
    □ g′ H = 
    rotate-cospan (substitute-homotopic-right-map (rotate-cospan □) g′ H)

  substitute-equivalent : 
    ∀ {Z A A′ B C : U₀} 
    {f : A → C}  {g : B → C}
    {z₁ : Z → A} {z₂ : Z → B}
    (e : A′ → A)
    → (e-is-an-equivalence : e is-an-equivalence)
    → pullback-square f g z₁ z₂
    → pullback-square (f ∘ e) g ((inverse-of e given-by e-is-an-equivalence) ∘ z₁) z₂ 
  substitute-equivalent {Z} {A} {A′} {B} {C} {f} {g} {z₁} {z₂} e
    (has-left-inverse e⁻¹l by left-invertibility and-right-inverse e⁻¹r by right-invertibility) 
    (the-square-commuting-by γ and-inducing-an-equivalence-by proof-of-equivalency) = 
    let 
      e⁻¹l∘e∼1 = left-invertibility
      e∘e⁻¹l∼1 : e ∘ e⁻¹l ∼ id
      e∘e⁻¹l∼1 = left-inverses-are-also-right-inverses e e⁻¹l e⁻¹r
                   left-invertibility right-invertibility

      new-square-commutes : (f ∘ e) ∘ (e⁻¹l ∘ z₁) ∼ g ∘ z₂
      new-square-commutes z = f ⁎ e∘e⁻¹l∼1 (z₁ z) • γ z
      
      induced-map : Z → pullback (f ∘ e) g
      induced-map = induced-map-to-pullback (e⁻¹l ∘ z₁) z₂ new-square-commutes

      old-induced-map : Z → pullback f g
      old-induced-map = induced-map-to-pullback z₁ z₂ γ
  
      induced-between-canonicals : pullback (f ∘ e) g → pullback f g
      induced-between-canonicals = equivalence-invariance.induced-map f g e
                                     (has-left-inverse e⁻¹l by left-invertibility and-right-inverse e⁻¹r
                                      by right-invertibility)
      
      induced-map-to-canonical-pullback-is-an-equivalence :
        induced-between-canonicals is-an-equivalence
      induced-map-to-canonical-pullback-is-an-equivalence =
          equivalence-invariance.the-induced-map-is-an-equivalence f g e
            (has-left-inverse e⁻¹l by left-invertibility and-right-inverse e⁻¹r
                                   by right-invertibility)
      
      2-out-of-3-setup : induced-between-canonicals ∘ induced-map ∼ old-induced-map 
      2-out-of-3-setup = uniqueness-of-induced-maps z₁ z₂ γ
                           (induced-between-canonicals ∘ induced-map) 
                           (λ z → e∘e⁻¹l∼1 (z₁ z))
                           (λ z → refl) (λ z → f ⁎ e∘e⁻¹l∼1 (z₁ z) ⁻¹ • (f ⁎ e∘e⁻¹l∼1 (z₁ z) • γ z) • refl
                                              ≈⟨ refl-is-right-neutral
                                                   (f ⁎ e∘e⁻¹l∼1 (z₁ z) ⁻¹ • (f ⁎ e∘e⁻¹l∼1 (z₁ z) • γ z)) ⁻¹ ⟩ 
                                               f ⁎ e∘e⁻¹l∼1 (z₁ z) ⁻¹ • (f ⁎ e∘e⁻¹l∼1 (z₁ z) • γ z)
                                              ≈⟨ •-is-associative (f ⁎ e∘e⁻¹l∼1 (z₁ z) ⁻¹) (f ⁎ e∘e⁻¹l∼1 (z₁ z)) (γ z) ⟩
                                               f ⁎ (e∘e⁻¹l∼1 (z₁ z)) ⁻¹ • f ⁎ e∘e⁻¹l∼1 (z₁ z) • γ z
                                              ≈⟨ (λ ξ → ξ • γ z) ⁎ ⁻¹-is-left-inversion (f ⁎ e∘e⁻¹l∼1 (z₁ z)) ⟩
                                               γ z ≈∎) 

      the-composition-is-an-equivalence :
        induced-between-canonicals ∘ induced-map is-an-equivalence
      the-composition-is-an-equivalence = 
        the-map (induced-between-canonicals ∘ induced-map) is-an-equivalence-since-it-is-homotopic-to
        old-induced-map by 2-out-of-3-setup which-is-an-equivalence-by proof-of-equivalency

      the-induced-map-is-an-equivalence : induced-map is-an-equivalence
      the-induced-map-is-an-equivalence =
        2-out-of-3.the-left-map-is-an-equivalence induced-map
          induced-between-canonicals the-composition-is-an-equivalence
          induced-map-to-canonical-pullback-is-an-equivalence
      
    in the-square-commuting-by new-square-commutes
       and-inducing-an-equivalence-by
         the-induced-map-is-an-equivalence




  substitute-equivalent-cone :
    ∀ {Z Z′ A B C : U₀} 
      {f : A → C} {g : B → C}
      {z₁ : Z → A} {z₂ : Z → B}
      (z₁′ : Z′ → A) (z₂′ : Z′ → B)
      (e : Z′ → Z)
    → e is-an-equivalence → (z₁ ∘ e ∼ z₁′) → (z₂ ∘ e ∼ z₂′)
    → pullback-square-with-right f bottom g top z₁ left z₂
    → pullback-square-with-right f bottom g top z₁′ left z₂′
  substitute-equivalent-cone {Z} {Z′} {_} {_} {_} {f} {g} {z₁} {z₂}
    z₁′ z₂′ e e-is-an-equivalence z₁∘e∼z₁′ z₂∘e∼z₂′
    (the-square-commuting-by γ and-inducing-an-equivalence-by old-induced-is-an-equivalence) =
    let 
      old-induced-map : Z → pullback f g
      old-induced-map = induced-map-to-pullback z₁ z₂ γ
      new-homotopy : f ∘ z₁′ ∼ g ∘ z₂′
      new-homotopy z = f ⁎ z₁∘e∼z₁′ z ⁻¹ • γ (e z) • g ⁎ z₂∘e∼z₂′ z 
      induced-map : Z′ → pullback f g
      induced-map = induced-map-to-pullback z₁′ z₂′ new-homotopy
      induced-map-is-an-equivalence : induced-map is-an-equivalence
      induced-map-is-an-equivalence = 
        equivalences-are-preserved-by-homotopy
          (old-induced-map ∘ e) induced-map 
          (the-composition-of-equivalences-is-an-equivalence e
            old-induced-map e-is-an-equivalence old-induced-is-an-equivalence) 
          (λ z → uniqueness-of-induced-maps z₁′ z₂′ new-homotopy
                   (old-induced-map ∘ e) z₁∘e∼z₁′ z₂∘e∼z₂′ (λ z → refl) z)
    in the-square-commuting-by new-homotopy and-inducing-an-equivalence-by 
       induced-map-is-an-equivalence

  substitute-equivalent-cone′ :
    ∀ {Z Z′ A B C : U₀} 
      {f : A → C} {g : B → C}
      {z₁ : Z → A} {z₂ : Z → B}
      (z₁′ : Z′ → A) (z₂′ : Z′ → B)
      (e : Z′ ≃ Z)
    → (z₁ ∘ (underlying-map-of e) ∼ z₁′) → (z₂ ∘ (underlying-map-of e) ∼ z₂′)
    → pullback-square-with-right f bottom g top z₁ left z₂
    → pullback-square-with-right f bottom g top z₁′ left z₂′
  substitute-equivalent-cone′ z₁ z₂ e = substitute-equivalent-cone z₁ z₂ (underlying-map-of e) (proof-of-equivalency e)

  substitute-homotopic-top-map :
    ∀ {Z A B C : U₀} 
     {f : A → C}  {g : B → C}
     {z₁ : Z → A} {z₂ : Z → B}
    → pullback-square f g z₁ z₂
    → (z₁′ : Z → A) → z₁′ ∼ z₁
    → pullback-square f g z₁′ z₂
  substitute-homotopic-top-map {Z} {A} {B} {C} {f} {g} {z₁} {z₂} 
    □ z₁′ H = 
    substitute-equivalent-cone z₁′ z₂ id id-is-an-equivalence (H ⁻¹⇒) (λ a → refl) □

  substitute-homotopic-left-map :
    ∀ {Z A B C : U₀} 
     {f : A → C}  {g : B → C}
     {z₁ : Z → A} {z₂ : Z → B}
    → pullback-square f g z₁ z₂
    → (z₂′ : Z → B) → z₂′ ∼ z₂
    → pullback-square f g z₁ z₂′
  substitute-homotopic-left-map {Z} {A} {B} {C} {f} {g} {z₁} {z₂} 
    □ z₂′ H = 
    substitute-equivalent-cone z₁ z₂′ id id-is-an-equivalence (λ a → refl) (H ⁻¹⇒) □


  _and_pull-back-the-same-cospan-so-the-first-may-be-replaced-by-the-second-in-the-square_ :
    ∀ {W Z A B C A′ B′ C′ : U₀}
      {f : A → C}  {g : B → C}
      {f′ : A′ → C′}  {g′ : B′ → C′}
      {z₁ : Z → A} {z₂ : Z → B}
      {z₁′ : Z → A′} {z₂′ : Z → B′}
      {w₁ : W → A} {w₂ : W → B}
      → (□₁ : pullback-square f g z₁ z₂)
      → (□₂ : pullback-square f g w₁ w₂)
      → (□ : pullback-square f′ g′ z₁′ z₂′)
      → pullback-square f′ g′ (z₁′ ∘ _) (z₂′ ∘ _)
  _and_pull-back-the-same-cospan-so-the-first-may-be-replaced-by-the-second-in-the-square_
    {W} {Z} {_} {_} {_} {_} {_} {_}
    {_} {_}
    {_} {_}
    {z₁} {z₂}
    {z₁′} {z₂′}
    {_} {_}
    □₁ □₂ □ =
      let
        φ′ : W ≃ Z
        φ′ = deduce-equivalence-of-vertices □₂ □₁
      
        φ = underlying-map-of φ′
        φ-is-an-equivalence = proof-of-equivalency φ′
        
      in substitute-equivalent-cone (z₁′ ∘ φ) (z₂′ ∘ φ) φ φ-is-an-equivalence (λ _ → refl)
           (λ _ → refl) □



  pullback-square-from-equivalence-of-maps :
    ∀ {A B A′ B′ : U₀}
    → (f : A → B) → (f′ : A′ → B′)
    → (eA : A′ ≃ A) → (eB : B′ ≃ B)
    → f ∘ (underlying-map-of eA) ⇒ (underlying-map-of eB) ∘ f′
    → pullback-square-with-right f bottom (underlying-map-of eB) top (underlying-map-of eA) left f′
  pullback-square-from-equivalence-of-maps {A} {A′} {_} {_} f f′ 
    (eA is-an-equivalence-because equivalency-of-eA)
    (eB is-an-equivalence-because equivalency-of-eB) γ =
    let
      -- idea: take an id-square and replace
      -- the identities by equivalences
      eB⁻¹ = inverse-of eB given-by equivalency-of-eB
      eB⁻¹∘eB⇒id = (_is-an-equivalence.unit equivalency-of-eB) 

      id-square : pullback-square-with-right id bottom f top f left id
      id-square = rotate-cospan (pullback-square-from-identity-of-morphisms f)

      fill-in-eB : pullback-square-with-right f bottom eB top id left (eB⁻¹ ∘ f)
      fill-in-eB = rotate-cospan
                     (substitute-equivalent eB equivalency-of-eB id-square)

      □₁ : pullback-square-with-right f bottom eB top eA left f′
      □₁ = substitute-equivalent-cone 
                           eA f′ eA equivalency-of-eA (λ a → refl) 
                           (λ a′ → eB⁻¹ ⁎ γ a′ • eB⁻¹∘eB⇒id (f′ a′)) fill-in-eB
                           
    in □₁

  {-
  
       pasting

        w₁    z₁
       W--> Z--> A
       |    |    |
       w₂   z₂   f
       |    |    |
       v h  v g  v
       D -> B -> C
  
  -}
  pasting-of-pullback-squares : 
    ∀ {W Z A B C D : U₀} 
    {f : A → C} {g : B → C} {h : D → B}
    {z₁ : Z → A} {z₂ : Z → B}
    {w₁ : W → Z} {w₂ : W → D}
    → (left-square : pullback-square-with-right z₂ bottom h top w₁ left w₂)
    → (right-square : pullback-square-with-right f bottom g top z₁ left z₂)
    → pullback-square-with-right f bottom (g ∘ h) top (z₁ ∘ w₁) left w₂
  pasting-of-pullback-squares {W} {Z} {A} {B} {C} {D} {f} {g} {h} {z₁} {z₂} {w₁} {w₂} 
    (the-square-commuting-by η and-inducing-an-equivalence-by proof-of-equivalence′) 
    (the-square-commuting-by γ and-inducing-an-equivalence-by proof-of-equivalence) 
    =
     let
        φ : Z → pullback f g
        φ = induced-map-to-pullback z₁ z₂ γ

        φ-as-equivalence : Z ≃ pullback f g
        φ-as-equivalence = φ is-an-equivalence-because proof-of-equivalence


        {-
                   p₁    z₁
           PB(p₂φ,h)→ Z--> A
           |  ψ|     φ|    |
           |PB(p₂,h)→ P-p₁→A
           \   |      |    |
            p₂ |     p₂    f
             \ |      |    |
              ↘|  h   ↓ g  ↓
               D----→ B---→C
        -}

        ψ : pullback (p₂ ∘ φ) h → pullback (p₂-of-pullback f g) h
        ψ = induced-map-to-pullback
              (φ ∘ p₁-of-pullback (p₂ ∘ φ) h)
              (p₂-of-pullback (p₂ ∘ φ) h)
              (λ x → p-homotopy x)

        ψ-is-an-equivalence : ψ is-an-equivalence
        ψ-is-an-equivalence =
          equivalence-invariance.the-induced-map-is-an-equivalence
            (p₂-of-pullback f g)
            h φ proof-of-equivalence
        
        
        -- the induced-map below is the map that needs to be an equivalence:
        composed-homotopy : f ∘ (z₁ ∘ w₁) ∼ (g ∘ h) ∘ w₂
        composed-homotopy z = γ (w₁ z) • g ⁎ η z

        induced-map : W → pullback f (g ∘ h)
        induced-map = induced-map-to-pullback (z₁ ∘ w₁) w₂ composed-homotopy

        {-

         Now look at the given induced equivalences
         χ : W to PB(z₂,h)=PB(p₂φ,h) and
         θ : PB(p₂,h) to PB(f,g∘h)  (given by canonical pasting)

         n.t.s: θ ∘ ψ ∘ χ is the induced map W → PB(f,g∘h)

        W----------w₁
        |\          \
        | χ          \
        |  ↘       p₁ ↘   z₁
        |  PB(p₂φ,h)→ Z--> A
        |  |  ψ|     φ|    |
        |  |PB(p₂,h)→ P-p₁→A
        w₂ \   |      |    |
        \   p₂ |     p₂    f
         \   \ |      |    |
          \   ↘|  h   ↓ g  ↓
           \--→D----→ B---→C
        -}

        χ : W → pullback (p₂ ∘ φ) h 
        χ = induced-map-to-pullback w₁ w₂ η

        θ : pullback (p₂-of-pullback f g) h ≃ pullback f (g ∘ h)
        θ = pasting-lemma f g h

        {-

        next step: use that ψ∘χ is homotopic to an induced map
        
        W -χ→ PB(p₂φ,h) -ψ→ PB(p₂,h) -θ→ PB(f,g∘h)
         \         ⇓H1      /
          \-----induced----/


        -}

        
        induced-to-iterated-pullback : W → pullback (p₂-of-pullback f g) h
        induced-to-iterated-pullback = induced-map-to-pullback (φ ∘ w₁) w₂ η

        H1 : ψ ∘ χ ∼ induced-to-iterated-pullback
        H1 w = refl

        -- conclude, that the induced map is an equivalence
        -- since χ and ψ are
        induced-map-to-iterated-pullback-is-an-equivalence : 
          induced-to-iterated-pullback is-an-equivalence
        induced-map-to-iterated-pullback-is-an-equivalence = 
          equivalences-are-preserved-by-homotopy 
            (ψ ∘ χ) induced-to-iterated-pullback 
            (the-composition-of-equivalences-is-an-equivalence 
               χ ψ proof-of-equivalence′ ψ-is-an-equivalence) 
            H1
        

        {-

        next step: use result in PullbackPasting to show that θ∘ψ∘χ 
         is homotopic to an induced map
        
        W -ψ∘χ→ PB(p₂,h) -θ→ PB(f,g∘h)
         \           ⇓H2        /
          \-------induced------/

        (this is the previously defined 'induced-map')
        -}

        H2 : (underlying-map-of θ) ∘ (ψ ∘ χ) ∼ induced-map
        H2 = proof-of-pullback-lemma.factor-induced-maps.induced-maps-factor 
               A B C D f g h W (φ ∘ w₁) w₂ η

        induced-equivalency : 
          induced-map is-an-equivalence
        induced-equivalency = 
          equivalences-are-preserved-by-homotopy 
           (underlying-map-of θ ∘ ψ ∘ χ) induced-map 
           (the-composition-of-equivalences-is-an-equivalence 
             (ψ ∘ χ) (underlying-map-of θ) 
             induced-map-to-iterated-pullback-is-an-equivalence 
             (proof-of-equivalency (pasting-lemma f g h))) (λ a → refl)
     in the-square-commuting-by composed-homotopy
        and-inducing-an-equivalence-by induced-equivalency




  cancel-right-pullback-square′ : 
    ∀ {W Z A B C D : U₀} 
    {f : A → C} {g : B → C} {h : D → B}
    {z₁ : Z → A} {z₂ : Z → B}
    {w₁ : W → Z} {w₂ : W → D}
    → (right-square : pullback-square-with-right f bottom g top z₁ left z₂)
    → (η : z₂ ∘ w₁ ∼ h ∘ w₂)
    → (the-square-with-right f bottom (g ∘ h) top (z₁ ∘ w₁) left w₂
       commuting-by
        (λ w → underlying-2-cell right-square (w₁ w) • g ⁎ η w)
       is-a-pullback-square)
    → pullback-square-with-right z₂ bottom h top w₁ left w₂
  cancel-right-pullback-square′  {W} {Z} {A} {B} {C} {D} {f} {g} {h} {z₁} {z₂} {w₁} {w₂} 
    (the-square-commuting-by γ and-inducing-an-equivalence-by proof-of-equivalence) 
    η
    (the-induced-map-is-an-equivalence-by outer-rectangle-is-a-pullback-square)
    =
     let
        φ : Z → pullback f g
        φ = induced-map-to-pullback z₁ z₂ γ

        φ-as-equivalence : Z ≃ pullback f g
        φ-as-equivalence = φ is-an-equivalence-because proof-of-equivalence


        {-
                   p₁    z₁
           PB(p₂φ,h)→ Z--> A
           |  ψ|     φ|    |
           |PB(p₂,h)→ P-p₁→A
           \   |      |    |
            p₂ |     p₂    f
             \ |      |    |
              ↘|  h   ↓ g  ↓
               D----→ B---→C
        -}

        ψ : pullback (p₂ ∘ φ) h → pullback (p₂-of-pullback f g) h
        ψ = induced-map-to-pullback
              (φ ∘ p₁-of-pullback (p₂ ∘ φ) h)
              (p₂-of-pullback (p₂ ∘ φ) h)
              (λ x → p-homotopy x)

        ψ-is-an-equivalence : ψ is-an-equivalence
        ψ-is-an-equivalence =
          equivalence-invariance.the-induced-map-is-an-equivalence
            (p₂-of-pullback f g)
            h φ proof-of-equivalence


        {-

         Now look at the given induced equivalences
         χ : W to PB(f,gh) and
         θ : PB(p₂,h) to PB(f,g∘h)  (given by canonical pasting)

        W-----------z₁∘w₁
        |\               \
        | χ               \
        |  ↘               ↘ 
        |  PB(p₂φ,g∘h)---> A
        |      |           |
        w₂     |           |
        \     p₂           f
         \     |           |
          \    ↓           ↓
           \--→D--h-→ B-g-→C
        -}

        χ : W → pullback f (g ∘ h)
        χ = induced-map-to-pullback (z₁ ∘ w₁) w₂ (λ w → γ (w₁ w) • g ⁎ η w)
        χ-as-equivalence = χ is-an-equivalence-because outer-rectangle-is-a-pullback-square
    
        θ : pullback f (g ∘ h) ≃ pullback (p₂-of-pullback f g) h
        θ = pasting-lemma f g h ⁻¹≃
        θ∘χ-is-an-equivalence = proof-of-equivalency (θ ∘≃ χ-as-equivalence)

        induced-to-iterated-pullback : W → pullback (p₂-of-pullback f g) h
        induced-to-iterated-pullback = induced-map-to-pullback (φ ∘ w₁) w₂ η

        -- now show that the last map is an equivalence
        -- (this follows from θ∘χ being an equivalence)
        
        induced-map-to-iterated-pullback-is-an-equivalence : 
          induced-to-iterated-pullback is-an-equivalence
        induced-map-to-iterated-pullback-is-an-equivalence = 
          equivalences-are-preserved-by-homotopy (underlying-map-of θ ∘ χ)
            induced-to-iterated-pullback θ∘χ-is-an-equivalence 
            (proof-of-pullback-lemma.factor-induced-maps.induced-maps-factor′ A B C D f g h W (φ ∘ w₁) w₂ η ⁻¹∼ )


        -- this induced-map is the map that needs to be an equivalence:
        induced-map : W → pullback z₂ h
        induced-map = induced-map-to-pullback w₁ w₂ η

        ψ∘induced-map∼induced-to-iterated-pullback :
          induced-to-iterated-pullback ∼ ψ ∘ induced-map 
        ψ∘induced-map∼induced-to-iterated-pullback w =
          refl
        

        the-induced-map-is-an-equivalence : induced-map is-an-equivalence
        the-induced-map-is-an-equivalence =
          let
            ψ∘induced-map-is-an-equivalence = equivalences-are-preserved-by-homotopy induced-to-iterated-pullback
                                                (ψ ∘ induced-map)
                                                induced-map-to-iterated-pullback-is-an-equivalence
                                                ψ∘induced-map∼induced-to-iterated-pullback
          in 2-out-of-3.the-left-map-is-an-equivalence induced-map ψ
               ψ∘induced-map-is-an-equivalence ψ-is-an-equivalence

     in the-square-commuting-by η and-inducing-an-equivalence-by the-induced-map-is-an-equivalence



  {-
     if the big rectangle is a pullback and the
     right square is a pullback, then the left 
     square is a pullback
    
         w₁    z₁
       W--> Z--> A
       |    |    |
       w₂   z₂   f
       |    |    |
       v h  v g  v
       D -> B -> C
  -}

  cancel-the-right-pullback-square_from_ : 
    ∀ {W Z A B C D : U₀} 
    {f : A → C} {g : B → C} {h : D → B}
    {z₁ : Z → A} {z₂ : Z → B}
    {w₁ : W → A} {w₂ : W → D}
    → (right-square : pullback-square-with-right f bottom g top z₁ left z₂)
    → (rectangle : pullback-square-with-right f bottom (g ∘ h) top w₁ left w₂)
    → pullback-square-with-right z₂ bottom h 
        top (induced-map-to-pullback-vertex right-square w₁ (h ∘ w₂) (underlying-2-cell rectangle)) 
        left w₂
  cancel-the-right-pullback-square_from_ {W} {Z} {A} {B} {C} {D} {f} {g} {h} {z₁} {z₂} {w₁} {w₂} 
    (the-square-commuting-by γ and-inducing-an-equivalence-by proof-of-equivalence) 
    (the-square-commuting-by η and-inducing-an-equivalence-by proof-of-equivalence′) 
    =
      {-
       obtain a factorization by using
       universality of the right pullback square

        w₁    
       W--> Z--z₁
       |\       ↘   
       | φ->P--> A
       |    |⌟   |
       w₂   p₂   f
       |    |    |
       v h  v g  v
       D -> B -> C

       φ is the induced map to the pullback of f and g
     -}
    let
      φ : W → pullback f g
      φ = induced-map-to-pullback w₁ (h ∘ w₂) η

      {-
      apply cancelling to the lower rectangle

       W
       |\
       | φ->P--> A
       |    |⌟   |
       w₂   p₂   f
       |    |    |
       v h  v g  v
       D -> B -> C

      -}

      the-lower-rectangle-is-a-pullback : induced-map-to-pullback w₁ w₂ (λ w → p-homotopy (φ w) • refl) is-an-equivalence
      the-lower-rectangle-is-a-pullback = transport (λ H → induced-map-to-pullback w₁ w₂ H is-an-equivalence)
                                    (fun-ext (λ w → refl-is-right-neutral (η w))) proof-of-equivalence′

      left-pullback-square : pullback-square-with-right p₂ bottom h top φ left w₂
      left-pullback-square = cancel-right-pullback-square′ (complete-to-pullback-square f g) 
                                 (λ w → refl) (the-induced-map-is-an-equivalence-by the-lower-rectangle-is-a-pullback)

      {-
       extends by the induced equivalence ψ

       W-w₁→Z
       |\   ↓ψ
       | φ->P
       |    |
       w₂   p₂
       |    |
       v h  v
       D -> B

      -}
      
      ψ : Z → pullback f g
      ψ = induced-map-to-pullback z₁ z₂ γ
      
      ψ⁻¹ : pullback f g → Z
      ψ⁻¹ = _is-an-equivalence.left-inverse proof-of-equivalence


      left-square′ : pullback-square-with-right z₂ bottom h top (ψ⁻¹ ∘ φ) left w₂
      left-square′ = substitute-equivalent ψ proof-of-equivalence left-pullback-square
    in left-square′


