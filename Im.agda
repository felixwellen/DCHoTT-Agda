{-# OPTIONS --without-K #-}

module Im where
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Contractibility
  open import Equivalences
  open import Sums using (dependent-curry)
  open import DependentTypes
  open import CommonEquivalences
  open import InfinityGroups
  open import FunctionExtensionality
  open import Pullback
  open import PullbackSquare
  open import Fiber
  open import Language
  open import Univalence                     -- for now, just convenience

  -- Axioms for ℑ, the infinitesimal shape modality
  -- (this may also be read as axiomatizing a general modality)

  postulate
    ℑ : ∀ {i} → 𝒰 i → 𝒰 i
    ℑ-unit : ∀ {i} {A : 𝒰 i} → A → ℑ A


  ℑ-unit-at :
    ∀ {i} → (A : 𝒰 i)
    → (A → ℑ A)
  ℑ-unit-at A = ℑ-unit {_} {A}

  ι : ∀ {i} {A : 𝒰 i}
    → A → ℑ A
  ι = ℑ-unit

  _is-coreduced : ∀ {i} → 𝒰 i → 𝒰 i
  A is-coreduced = ℑ-unit {_} {A} is-an-equivalence

  ℑ𝒰₀ : 𝒰₁
  ℑ𝒰₀ = ∑ λ (A : 𝒰₀) → A is-coreduced

  ι-ℑ𝒰₀ : ℑ𝒰₀ → 𝒰₀
  ι-ℑ𝒰₀ (A , _) = A

  postulate
    -- ℑ is idempotent
    ℑ-is-coreduced : ∀ {i} → (A : 𝒰 i) → (ℑ A) is-coreduced

    ℑ-induction :
      ∀ {i} {A : 𝒰₀} {B : ℑ A → 𝒰 i}
      → (∀ (a : ℑ A) → B(a) is-coreduced)
      → ((a : A) → B(ℑ-unit a))
      → ((a : ℑ A) → B(a))
    ℑ-compute-induction :
      ∀ {A : 𝒰₀} {B : ℑ A → 𝒰₀}
      → (coreducedness : ∀ (a : ℑ A) → B(a) is-coreduced)
      → (f : (a : A) → B(ℑ-unit a))
      → (a : A) → (ℑ-induction coreducedness f) (ℑ-unit a) ≈ f a

    coreduced-types-have-coreduced-identity-types :
      ∀ (B : 𝒰₀) → (B is-coreduced) → (b b′ : B)
      → (b ≈ b′) is-coreduced


    {- this is a way to state left exactness of ℑ
       and for now, it is the only way we need left exactness -}

    ℑ𝒰₀-is-coreduced : ℑ𝒰₀ is-coreduced

  -- End Axioms


  ℑ-recursion :
    ∀ {i} {A : 𝒰₀} {B : 𝒰 i}
    → B is-coreduced
    → (f : A → B)
    → (ℑ A → B)
  ℑ-recursion coreducedness f = ℑ-induction (λ a → coreducedness) (λ a → f a)

  ℑ-compute-recursion :
    ∀ {A B : 𝒰₀}
    → (coreducedness : B is-coreduced)
    → (f : A → B)
    → (a : A) → (ℑ-recursion coreducedness f) (ℑ-unit a) ≈ f a
  ℑ-compute-recursion coreducedness f = ℑ-compute-induction (λ a → coreducedness) f

  apply-ℑ-to-map :
    ∀ {A B : 𝒰₀}
    → (A → B)
    → (ℑ A → ℑ B)
  apply-ℑ-to-map {_} {B} f = ℑ-recursion (ℑ-is-coreduced B) (ℑ-unit-at B ∘ f)

  apply-ℑ : ∀ {A B : 𝒰₀}
            → (A → B)
            → (ℑ A → ℑ B)
  apply-ℑ f = apply-ℑ-to-map f

  ℑ→ = apply-ℑ

  naturality-square-for-ℑ :
    ∀ {A B : 𝒰₀}
    → (f : A → B)
    → (a : A) → (apply-ℑ-to-map f(ℑ-unit {_} {A} a) ≈ ℑ-unit {_} {B}(f a))
  naturality-square-for-ℑ {_} {B} f = ℑ-compute-recursion (ℑ-is-coreduced B) (λ z → ℑ-unit (f z))

  naturality-of-ℑ-unit :
    ∀ {A B : 𝒰₀}
    → (f : A → B)
    → (ℑ→ f) ∘ ι  ⇒ ι ∘ f
  naturality-of-ℑ-unit {_} {B} f = ℑ-compute-recursion (ℑ-is-coreduced B) (λ z → ℑ-unit (f z))

  ℑ⇒ : ∀ {A B : 𝒰₀} {f g : A → B}
       → (f ⇒ g) → (ℑ→ f ⇒ ℑ→ g)
  ℑ⇒ H = ℑ-induction
         (λ a → coreduced-types-have-coreduced-identity-types (ℑ _) (ℑ-is-coreduced _) (ℑ→ _ a) (ℑ→ _ a))
         (λ a → naturality-square-for-ℑ _ a • ℑ-unit ⁎ (H a) • naturality-square-for-ℑ _ a ⁻¹)

  ℑ⁎_⁎_ :
    ∀ {A B : 𝒰₀} {x y : A}
    → (f : A → B)
    → ι x ≈ ι y
    → ι (f x) ≈ ι (f y)
  ℑ⁎ f ⁎ γ = naturality-square-for-ℑ f _ ⁻¹ • ℑ→ f ⁎ γ • naturality-square-for-ℑ f _

  -- define coreduced connectedness
  _is-ℑ-connected :
    ∀ {A B : 𝒰₀} (f : A → B)
    → 𝒰₀
  _is-ℑ-connected {_} {B} f  = ∀ (b : B) → ℑ (fiber-of f at b) is-contractible

  ℑ-induction-as-equivalence :
      ∀ {A : 𝒰₀} {B : ℑ A → 𝒰₀}
      → (∀ (a : ℑ A) → B(a) is-coreduced)
      → ((a : ℑ A) → B(a)) ≃ ((a : A) → B(ι a))
  ℑ-induction-as-equivalence B-is-coreduced = (λ s → λ x → s (ι x))
    is-an-equivalence-because
      (has-left-inverse (λ s → ℑ-induction B-is-coreduced s)
        by (λ s → fun-ext
          (ℑ-induction (λ a → coreduced-types-have-coreduced-identity-types _ (B-is-coreduced _) _ _)
          (λ a → ℑ-compute-induction B-is-coreduced (λ x → s (ι x)) a)))
       and-right-inverse (λ s → ℑ-induction B-is-coreduced s)
         by (λ s → fun-ext (λ a → ℑ-compute-induction B-is-coreduced s a ⁻¹)))

  ℑ-recursion-is-unique :
    ∀ {A B : 𝒰₀} (f : A → B) (coreducedness : B is-coreduced)
    → (φ : ℑ A → B) → f ⇒ φ ∘ ℑ-unit
    → ℑ-recursion coreducedness f ⇒ φ
  ℑ-recursion-is-unique {A} {B} f coreducedness φ φ-factors =
    let
        factor-over-unit : (A → B) → (ℑ A → B)
        factor-over-unit = ℑ-recursion coreducedness
        factoring-is-nice : ∀ (g : ℑ A → B)
                            → factor-over-unit (g ∘ ℑ-unit) ⇒ g
        factoring-is-nice g =
          let
            true-on-constructed = ℑ-compute-recursion coreducedness (g ∘ ℑ-unit)
          in ℑ-induction
               (λ x → coreduced-types-have-coreduced-identity-types
                        B coreducedness (factor-over-unit (g ∘ ℑ-unit) x) (g x))
               true-on-constructed
        induced-map = ℑ-recursion coreducedness f
        both-factor-the-same-map : induced-map ∘ ℑ-unit ⇒ φ ∘ ℑ-unit
        both-factor-the-same-map = compose-homotopies (ℑ-compute-recursion coreducedness f) φ-factors
    in compose-homotopies
        (reverse-homotopy (factoring-is-nice induced-map))
        (compose-homotopies
           (mapping-preserves-homotopy factor-over-unit both-factor-the-same-map)
           (factoring-is-nice φ))


  module ℑ-is-idempotent (E : 𝒰₀) (E-is-coreduced : E is-coreduced) where
  -- 'idempotency for ℑ'
  -- here, we merely define the inverse to the equivalence appearing in
  -- the axiom stating that ℑA is coreduced, for all A

    ℑ-unit⁻¹ : ℑ E → E
    ℑ-unit⁻¹ = ℑ-recursion E-is-coreduced id

    left-invertible : ℑ-unit⁻¹ ∘ ℑ-unit ⇒ id
    left-invertible = ℑ-compute-recursion E-is-coreduced id

  cancel-one-ℑ-on :
    ∀ (A : 𝒰₀)
    → ℑ (ℑ A) → ℑ A
  cancel-one-ℑ-on A = ℑ-recursion (ℑ-is-coreduced A) id

  apply-ℑ-commutes-with-∘ :
    ∀ {A B C : 𝒰₀}
    → (f : A → B) → (g : B → C)
    → apply-ℑ (g ∘ f) ⇒ (apply-ℑ g) ∘ (apply-ℑ f)
  apply-ℑ-commutes-with-∘ f g =
    ℑ-recursion-is-unique
           (ℑ-unit ∘ (g ∘ f))
           (ℑ-is-coreduced _)
           (apply-ℑ g ∘ apply-ℑ f)
           (λ a → naturality-square-for-ℑ g (f a) ⁻¹
                  • (λ x → apply-ℑ g x) ⁎ naturality-square-for-ℑ f a ⁻¹)

  applying-ℑ-preserves-id : ∀ (A : 𝒰₀)
                            → apply-ℑ (id {_} {A}) ⇒ id {_} {ℑ A}
  applying-ℑ-preserves-id A =
    ℑ-recursion-is-unique (ℑ-unit ∘ id {_} {A}) (ℑ-is-coreduced A) id (λ _ → refl)

  applying-ℑ-preserves-equivalences : ∀ {A B : 𝒰₀} (f : A → B)
                                      → f is-an-equivalence
                                      → (ℑ→ f) is-an-equivalence
  applying-ℑ-preserves-equivalences f witness =
    let ℑf = apply-ℑ f
        l = (_is-an-equivalence.left-inverse witness)
        r = (_is-an-equivalence.right-inverse witness)
        ℑl = apply-ℑ l
        ℑr = apply-ℑ r

        unit : ℑl ∘ ℑf ∼ id
        unit = compose-homotopies (reverse-homotopy (apply-ℑ-commutes-with-∘ f l))
                   (ℑ-recursion-is-unique (ℑ-unit ∘ (l ∘ f)) (ℑ-is-coreduced _) id
                    (_is-an-equivalence.unit witness right-whisker ℑ-unit))

        counit : id ∼ ℑf ∘ ℑr
        counit = compose-homotopies
                   (reverse-homotopy (ℑ-recursion-is-unique (ℑ-unit ∘ (f ∘ r)) (ℑ-is-coreduced _) id
                    ((reverse-homotopy (_is-an-equivalence.counit witness)) right-whisker ℑ-unit)))
                   (apply-ℑ-commutes-with-∘ r f)

    in has-left-inverse
         ℑl by unit
       and-right-inverse
         ℑr by counit

  apply-ℑ-to-the-equivalence : ∀ {A B : 𝒰₀}
                               → A ≃ B → ℑ A ≃ ℑ B
  apply-ℑ-to-the-equivalence
    (f is-an-equivalence-because proof-of-invertibility) =
      (ℑ→ f) is-an-equivalence-because
        applying-ℑ-preserves-equivalences f proof-of-invertibility

  -- shorthand
  ℑ≃ : ∀ {A B : 𝒰₀}
    → A ≃ B → ℑ A ≃ ℑ B
  ℑ≃ = apply-ℑ-to-the-equivalence

  -- this is put to use later to conclude that equivalences can 'move' formal disks
  module equivalences-induce-equivalences-on-the-coreduced-identity-types {A B : 𝒰₀} (f≃ : A ≃ B) (x y : A) where
    f = underlying-map-of f≃
    ℑf⁎ : ℑ-unit(x) ≈ ℑ-unit(y) → ℑ-unit(f x) ≈ ℑ-unit(f y)
    ℑf⁎ = λ γ → (ℑ⁎ f ⁎ γ)
    ℑf⁎′ : ℑ-unit(x) ≈ ℑ-unit(y) → ℑ→ f (ℑ-unit x) ≈ ℑ→ f (ℑ-unit y)
    ℑf⁎′ γ = ℑ→ f ⁎ γ
    ℑf⁎′-is-an-equivalence : ℑf⁎′ is-an-equivalence
    ℑf⁎′-is-an-equivalence =
      proof-that-equivalences-induce-equivalences-on-path-spaces.proof
        (ℑ A) (ℑ B) (apply-ℑ-to-the-equivalence f≃)

    {-
      we want to show that ℑf⁎ is an equivalence
      it is the composition of ℑf (induced one on path spaces)
      and conjugation with a naturality path for ℑ
      so we have to show, that this conjugation is an equivalence
    -}

    conjugate : ℑ→ f (ℑ-unit x) ≈ ℑ→ f (ℑ-unit y) → ℑ-unit(f x) ≈ ℑ-unit(f y)
    conjugate γ = naturality-square-for-ℑ f _ ⁻¹ • γ • naturality-square-for-ℑ f _

    conjugate⁻¹ : ℑ-unit(f x) ≈ ℑ-unit(f y) → ℑ→ f (ℑ-unit x) ≈ ℑ→ f (ℑ-unit y)
    conjugate⁻¹ γ = naturality-square-for-ℑ f _ • γ • naturality-square-for-ℑ f _ ⁻¹

    conjugate⁻¹∘conjugate⇒id : conjugate⁻¹ ∘ conjugate ⇒ id
    conjugate⁻¹∘conjugate⇒id γ =
        (naturality-square-for-ℑ f _) • ((naturality-square-for-ℑ f _) ⁻¹ • γ • naturality-square-for-ℑ f _) • naturality-square-for-ℑ f _ ⁻¹
      ≈⟨ stupid-but-necessary-calculation-with-associativity γ
           (naturality-square-for-ℑ f _) (naturality-square-for-ℑ f _) ⟩
        γ
      ≈∎

    conjugate∘conjugate⁻¹⇒id : conjugate ∘ conjugate⁻¹ ⇒ id
    conjugate∘conjugate⁻¹⇒id γ =
        (naturality-square-for-ℑ f _ ⁻¹) • ((naturality-square-for-ℑ f _) • γ • naturality-square-for-ℑ f _ ⁻¹) • naturality-square-for-ℑ f _
      ≈⟨ another-stupid-but-necessary-calculation-with-associativity γ  (naturality-square-for-ℑ f _) (naturality-square-for-ℑ f _) ⟩
        γ
      ≈∎

    --
    conjugation-with-naturality-path-is-an-equivalence :
      conjugate is-an-equivalence
    conjugation-with-naturality-path-is-an-equivalence =
      has-left-inverse conjugate⁻¹ by conjugate⁻¹∘conjugate⇒id
      and-right-inverse conjugate⁻¹ by conjugate∘conjugate⁻¹⇒id ⁻¹⇒

    ℑf⁎-is-an-equivalence : ℑf⁎ is-an-equivalence
    ℑf⁎-is-an-equivalence =
      the-composition-of ℑf⁎′ and conjugate
        is-an-equivalence,-since-the-first-one-is-by ℑf⁎′-is-an-equivalence
        and-the-second-by conjugation-with-naturality-path-is-an-equivalence



  module the-ℑ-preimages-of-equivalences-are-ℑ-connected -- not yet complete, not needed anyway
    {A B : 𝒰₀} (f : A → B) (ℑf-is-an-equivalence : (ℑ→ f) is-an-equivalence) where

    ℑf = ℑ→ f

    fiber-inclusion-at : ∀ (b : B) → fiber-of f at b → A
    fiber-inclusion-at b (a is-in-the-fiber-by γ) = a

    fiber-inclusion-composes-to-constant-map :
      ∀ (b : B) → f ∘ (fiber-inclusion-at b) ⇒ (λ _ → b)
    fiber-inclusion-composes-to-constant-map b (a is-in-the-fiber-by γ) = γ

    the-image-factors-over-the-point :
      ∀ (b : B)
      → ℑf ∘ (ℑ→ (fiber-inclusion-at b)) ⇒ ℑ→ (λ _ → b)
    the-image-factors-over-the-point b =
      (apply-ℑ-commutes-with-∘ (fiber-inclusion-at b) f ⁻¹⇒) •⇒ (ℑ⇒ (fiber-inclusion-composes-to-constant-map b))
{-
    conclusion : f is-ℑ-connected
    conclusion = {!!}
-}


  {-
    This helps to compute ℑA.
    For example when A is ∑P
  -}
  ℑ-yoneda :
    ∀ {A B : 𝒰₀} (f : A → B)
    → B is-coreduced
    → ((C : 𝒰₀) (p : C is-coreduced) → (λ (h : B → C) → h ∘ f) is-an-equivalence)   -- (B → C) ≃ (A → C)
    → ℑ A ≃ B
  ℑ-yoneda {A} {B} f B-is-coreduced B-has-the-universal-property-of-ℑ =
    let {- do what you learn in ct textbooks -}
        -∘f : (B → ℑ A) → (A → ℑ A)
        -∘f = (λ (h : B → ℑ A) → h ∘ f)

        -∘f⁻¹-is-an-equivalence = (B-has-the-universal-property-of-ℑ (ℑ A) (ℑ-is-coreduced A))
        -∘f⁻¹ : (A → ℑ A) → (B → ℑ A)
        -∘f⁻¹ = right-inverse-of -∘f given-by -∘f⁻¹-is-an-equivalence

        φ : B → ℑ A
        φ = (right-inverse-of -∘f given-by -∘f⁻¹-is-an-equivalence) ι

        uniqueness-from-universal-property :
          ∀ (h : B → B)
          → h ∘ f ⇒ f
          → id ⇒ h
        uniqueness-from-universal-property h H x =
          (λ z → z x) ⁎ equivalences-are-injective (B-has-the-universal-property-of-ℑ B B-is-coreduced) (fun-ext H) ⁻¹

        ψ : ℑ A → B
        ψ = ℑ-recursion B-is-coreduced f

        ι⇒φ∘ψ∘ι : ι ⇒ φ ∘ ψ ∘ ι
        ι⇒φ∘ψ∘ι a = ι a
                  ≈⟨ (λ z → z a) ⁎ (counit-of -∘f given-by -∘f⁻¹-is-an-equivalence) ι  ⟩
                   φ (f a)
                  ≈⟨ φ ⁎ ℑ-compute-recursion B-is-coreduced f a ⁻¹ ⟩
                   φ (ψ (ι a))
                  ≈∎

        φ∘ψ⇒id : φ ∘ ψ ⇒ id
        φ∘ψ⇒id = ℑ-recursion-is-unique ι (ℑ-is-coreduced A) (φ ∘ ψ) ι⇒φ∘ψ∘ι ⁻¹⇒  •⇒ applying-ℑ-preserves-id A

        id⇒ψ∘φ : id ⇒ ψ ∘ φ
        id⇒ψ∘φ = uniqueness-from-universal-property (ψ ∘ φ)
          (λ a →   ψ (φ (f a))
                 ≈⟨ ψ ⁎ ((λ z → z a) ⁎ (counit-of -∘f given-by -∘f⁻¹-is-an-equivalence) ι ⁻¹) ⟩
                   ψ (ι a)
                 ≈⟨ ℑ-compute-recursion B-is-coreduced f a ⟩
                   f a
                 ≈∎)

    in ψ is-an-equivalence-because
      (has-left-inverse φ by φ∘ψ⇒id and-right-inverse φ by id⇒ψ∘φ)

  types-equivalent-to-their-coreduction-are-coreduced :
    ∀ {A : 𝒰₀} (f : A ≃ ℑ A)
    → ℑ-unit-at A is-an-equivalence
  types-equivalent-to-their-coreduction-are-coreduced {A} f =
    let f⁻¹-as-map = underlying-map-of (f ⁻¹≃)
        f-as-map = underlying-map-of f
        ℑf⁻¹ = ℑ→ f⁻¹-as-map
        ℑf = ℑ→ f-as-map
        the-composition = ℑf⁻¹ ∘ (ℑ-unit {_} {ℑ A} ∘ f-as-map)
        the-composition-is-an-equivalence : the-composition is-an-equivalence
        the-composition-is-an-equivalence = proof-of-equivalency
                                              (apply-ℑ-to-the-equivalence (f ⁻¹≃) ∘≃
                                               (ℑ-unit is-an-equivalence-because (ℑ-is-coreduced _)) ∘≃ f)

        step1 : the-composition ∼ ℑf⁻¹ ∘ (ℑf ∘ ℑ-unit-at A)
        step1 a = (λ x → ℑf⁻¹ x) ⁎ naturality-square-for-ℑ f-as-map a ⁻¹

        step2 : ℑf⁻¹ ∘ (ℑf ∘ ℑ-unit-at A) ∼ ℑ-unit-at A
        step2 a = _is-an-equivalence.unit
                    (proof-of-equivalency (apply-ℑ-to-the-equivalence f))
                    (ℑ-unit a)

    in  equivalences-are-preserved-by-homotopy the-composition (ℑ-unit-at A)
          the-composition-is-an-equivalence (compose-homotopies step1 step2)


  ℑ-𝟙-is-contractible : (ℑ 𝟙) is-contractible
  ℑ-𝟙-is-contractible =
    let ∗̂ = (id ∘ ℑ-unit {_} {𝟙}) ∗
        constant-∗̂ : ∀ {A : 𝒰₀} → A → ℑ 𝟙
        constant-∗̂ = λ x → ∗̂

        id∘ℑ-unit∼constant-∗̂ : id ∘ ℑ-unit ∼ constant-∗̂
        id∘ℑ-unit∼constant-∗̂ = λ {∗ → refl}

        factored-trivial-map = ℑ-recursion (ℑ-is-coreduced 𝟙) (id ∘ ℑ-unit)

        step1 : factored-trivial-map ∼ id
        step1 = ℑ-recursion-is-unique
              (id ∘ ℑ-unit) (ℑ-is-coreduced 𝟙) id (λ a → refl)

        step2 : factored-trivial-map ∼ constant-∗̂
        step2 = ℑ-recursion-is-unique (id ∘ ℑ-unit) (ℑ-is-coreduced 𝟙)
                constant-∗̂ id∘ℑ-unit∼constant-∗̂

        step3 : id ∼ constant-∗̂
        step3 = compose-homotopies (reverse-homotopy step1) step2

    in reformulate-contractibilty-as-homotopy (ℑ 𝟙) ∗̂
       step3



  -- the hott book told me the following is true:
  retracts-of-coreduced-types-are-coreduced :
    ∀ (A E : 𝒰₀) → (E is-coreduced)
    → (ι : A → E) (r : E → A)
    → r ∘ ι ⇒ id
    → (ℑ-unit-at A) is-an-equivalence
  -- and tobi explained a proof to me:
  retracts-of-coreduced-types-are-coreduced A E E-is-coreduced ι r R =
    let
      ℑ-unit-E = ℑ-unit is-an-equivalence-because E-is-coreduced
      l-inverse′ = left-inverse-of-the-equivalence ℑ-unit-E
      r-inverse′ = right-inverse-of-the-equivalence ℑ-unit-E
      unit′ = unit-of-the-equivalence ℑ-unit-E
      counit′ = counit-of-the-equivalence ℑ-unit-E
      ℑι = apply-ℑ ι
      ℑr = apply-ℑ r
      ℑR = compose-homotopies (reverse-homotopy (apply-ℑ-commutes-with-∘ ι r))
                   (ℑ-recursion-is-unique (ℑ-unit ∘ (r ∘ ι)) (ℑ-is-coreduced _) id
                    (R right-whisker ℑ-unit))
      -- left and right inverses to ℑ-unit {A}
      l-inverse = r ∘ l-inverse′ ∘ ℑι
      r-inverse = r ∘ r-inverse′ ∘ ℑι
    in has-left-inverse l-inverse by
         (λ a → (λ x → r (l-inverse′ x)) ⁎ naturality-square-for-ℑ ι a
           • ((λ x → r x) ⁎ unit′ (ι a) • R a))
       and-right-inverse r-inverse by
         (λ â → ℑR â ⁻¹ • ((λ x → ℑr x) ⁎ counit′ (ℑι â)
           • naturality-square-for-ℑ r (r-inverse′ (ℑι â))))


  -- from the book "7.7 Modalities"
  module Π-of-coreduced-types-is-coreduced
    {A : 𝒰₀} (P : A → 𝒰₀)
    (P-is-coreduced : (a : A) → (P a) is-coreduced) where

    inverse : ℑ(Π(λ a → ℑ(P a))) → Π(λ a → ℑ(P a))
    inverse f̂ a =
                  let ℑπₐ : ℑ(Π(λ a → ℑ(P a))) → ℑ(P a)
                      ℑπₐ = (ℑ-is-idempotent.ℑ-unit⁻¹ (ℑ (P a)) (ℑ-is-coreduced (P a)))
                                  ∘ apply-ℑ-to-map (π-Π a)
                  in ℑπₐ f̂


    coreducedness′ : Π(λ a → ℑ(P a)) is-coreduced
    coreducedness′ = retracts-of-coreduced-types-are-coreduced
               (Π (λ a → ℑ (P a))) (ℑ (Π (λ a → ℑ (P a)))) (ℑ-is-coreduced (Π(λ a → ℑ (P a))))
               ℑ-unit inverse (λ f →
                                   fun-ext
                                   (λ a →
                                      ℑ-is-idempotent.ℑ-unit⁻¹ (ℑ (P a)) (ℑ-is-coreduced (P a)) ⁎
                                      naturality-square-for-ℑ (π-Π a) f
                                      • ℑ-is-idempotent.left-invertible (ℑ (P a)) (ℑ-is-coreduced (P a)) (f a)))

    coreducedness : Π(λ a → P a) is-coreduced
    coreducedness = transport
                      (λ (X : 𝒰₀) → X is-coreduced)
                      (Π ⁎ fun-ext (λ (a : A) → univalence (ℑ-unit-at (P a) is-an-equivalence-because (P-is-coreduced a)) ⁻¹))
                      coreducedness′


  {- experiment for lex modalities -}
  module identity-types-of-sums
    {A : 𝒰₀} (P : A → 𝒰₀) where

    ℑ-transport′ : {a a′ : A}
      → ℑ (a ≈ a′) → (ℑ (P a) →  ℑ (P a′))
    ℑ-transport′ {a} {a′} =
      ℑ-induction
        (λ (γ : ℑ (a ≈ a′)) → Π-of-coreduced-types-is-coreduced.coreducedness
          (λ _ → ℑ (P a′)) (λ _ → ℑ-is-coreduced _))
        (λ (γ : a ≈ a′) → ℑ→ (transport P γ))

    postulate
      ℑ-is-lex : ∀ (a a′ : A) → ι a ≈ ι a′ → ℑ (a ≈ a′)

    ℑ-transport : {a a′ : A}
      → (ι a ≈ ι a′) → (ℑ (P a) →  ℑ (P a′))
    ℑ-transport = ℑ-transport′ ∘ (ℑ-is-lex _ _)

{-
    encode : {a a′ : A} {pₐ : P a} {pₐ′ : P a′} →
      ι (a , pₐ) ≈ ι (a′ , pₐ′)
     →
      ∑ (λ (γ : ι a ≈ ι a′) → (ℑ-transport γ (ι pₐ) ≈ ι pₐ′))
    encode γ = (naturality-of-ℑ-unit ∑π₁ _ ⁻¹ • (ℑ→ ∑π₁) ⁎ γ • naturality-of-ℑ-unit _ _  , {!!})

    result : (x y : ∑ P) →
      ι x ≈ ι y
     ≃
      ∑ (λ (γ : ι (∑π₁ x) ≈ ι (∑π₁ y)) → (ℑ-transport γ (ι (∑π₂ x)) ≈ ι (∑π₂ y)))
    result = {!!}
-}


  -- from the book, thm 7.7.4
  ∑-of-coreduced-types-is-coreduced :
    ∀ (E : 𝒰₀)
    → (E is-coreduced) → (P : E → 𝒰₀)
    → ((e : E) → (P e) is-coreduced)
    → (∑ P) is-coreduced
  ∑-of-coreduced-types-is-coreduced E E-is-coreduced P P-is-coreduced =
    let
        ℑπ : ℑ(∑ P) → ℑ E
        ℑπ = apply-ℑ-to-map (λ {(e , _) → e})

        ℑ-unit-E = ℑ-unit is-an-equivalence-because E-is-coreduced
        ℑ-unit-E⁻¹ = ℑ-unit-E ⁻¹≃

        π : ∑ P → E
        π = λ {(e , _) → e}

        π′ : ℑ (∑ P) → E
        π′ = underlying-map-of ℑ-unit-E⁻¹ ∘ ℑπ

        π-is-compatible-to-π′ : π ∼ π′ ∘ ℑ-unit
        π-is-compatible-to-π′ x = unit-of-the-equivalence ℑ-unit-E (π x) ⁻¹
                                  • underlying-map-of ℑ-unit-E⁻¹ ⁎ naturality-square-for-ℑ π x ⁻¹

        P′ : ℑ (∑ P) → 𝒰₀
        P′ p̂ = P (π′ p̂)

        -- construct a section of the bundle '∑ P → ℑ ∑ P'
        -- (which will expose '∑ P' as a retract of 'ℑ ∑ P')
        section-on-ℑ-image : (x : ∑ P) → P (π′(ℑ-unit x))
        section-on-ℑ-image = λ { (e , p) → transport P (π-is-compatible-to-π′ (e , p)) p }
        section : (p̂ : ℑ (∑ P)) → P′ p̂
        section = ℑ-induction (λ p̂ → P-is-coreduced (π′ p̂)) section-on-ℑ-image

        r : ℑ (∑ P) → ∑ P
        r x = ((π′ x) , (section x))

        calculate1 : ∀ (x : ∑ P) → r(ℑ-unit x) ≈ ((π′ (ℑ-unit x)) , (section-on-ℑ-image x))
        calculate1 x = (λ z → (π′ (ℑ-unit x) , z)) ⁎
                        ℑ-compute-induction (λ p̂ → P-is-coreduced (π′ p̂)) section-on-ℑ-image
                        x
        π₂ : (x : ∑ P) → P (π x)
        π₂ = λ {(_ , p) → p}
        calculate2 : ∀ (x : ∑ P)
                     → in-the-type (∑ P) we-have-an-equality
                       ((π′ (ℑ-unit x)) , (section-on-ℑ-image x)) ≈ ((π x) , (π₂ x))
        calculate2 x =
          let γ = π-is-compatible-to-π′ x
          in construct-path-in-∑ (π x) (π′ (ℑ-unit x)) (π₂ x)
               (section-on-ℑ-image x) γ refl
               ⁻¹
        ℑ∑P-is-a-retract : r ∘ ℑ-unit-at (∑ P) ∼ id
        ℑ∑P-is-a-retract = compose-homotopies calculate1 calculate2
    in retracts-of-coreduced-types-are-coreduced (∑ P) (ℑ (∑ P)) (ℑ-is-coreduced _)
         ℑ-unit r ℑ∑P-is-a-retract



  cancel-ℑ-of-∑ :
    ∀ (E : 𝒰₀)
    → (E is-coreduced) → (P : E → 𝒰₀)
    → ((e : E) → (P e) is-coreduced)
    → ∑ P ≃ ℑ (∑ P)
  cancel-ℑ-of-∑ E E-is-coreduced P P-is-coreduced =
    (ℑ-unit is-an-equivalence-because
      ∑-of-coreduced-types-is-coreduced E E-is-coreduced P P-is-coreduced)

  canonical-pullback-of-coreduced-types-is-coreduced :
    ∀ {A B C : 𝒰₀} {f : A → C} {g : B → C}
    → pullback (ℑ→ f) (ℑ→ g) is-coreduced
  canonical-pullback-of-coreduced-types-is-coreduced {A} {B} {C} {f} {g} =
    let
      ℑA×ℑB-is-coreduced = ∑-of-coreduced-types-is-coreduced
                           (ℑ A) (ℑ-is-coreduced A) (λ _ → ℑ B) (λ _ → ℑ-is-coreduced B)
    in types-equivalent-to-their-coreduction-are-coreduced
          ( pullback (ℑ→ f) (ℑ→ g)
           ≃⟨ simple-reformulation.as-sum (ℑ→ f) (ℑ→ g) ⟩
            ∑ (simple-reformulation.fibration (ℑ→ f) (ℑ→ g))
           ≃⟨ cancel-ℑ-of-∑ (ℑ A × ℑ B)
                            (ℑA×ℑB-is-coreduced)
                            (λ { (á , b́) → (ℑ→ f) á ≈ (ℑ→ g) b́ })
                            ((λ { (á , b́) → coreduced-types-have-coreduced-identity-types (ℑ C) (ℑ-is-coreduced C) _ _ })) ⟩
            ℑ (∑ (simple-reformulation.fibration (ℑ→ f) (ℑ→ g)))
           ≃⟨ (apply-ℑ-to-the-equivalence (simple-reformulation.as-sum (ℑ→ f) (ℑ→ g))) ⁻¹≃ ⟩
            ℑ (pullback (ℑ→ f) (ℑ→ g))
           ≃∎)


  to-show-that_is-coreduced,-it-suffices-to-show-that_is-coreduced-since-it-is-equivalent-by_ :
    ∀ (A B : 𝒰₀)
    → (A ≃ B) → (B is-coreduced → A is-coreduced)
  to-show-that A is-coreduced,-it-suffices-to-show-that B is-coreduced-since-it-is-equivalent-by φ =
    transport _is-coreduced (univalence (φ ⁻¹≃))


  homotopies-in-coreduced-types-are-coreduced :
      ∀ {A B : 𝒰₀} {f g : ℑ A → ℑ B} → (f ⇒ g) is-coreduced
  homotopies-in-coreduced-types-are-coreduced {A} {B} {_} {_} =
      Π-of-coreduced-types-is-coreduced.coreducedness _
        (λ (a : ℑ A) →
          coreduced-types-have-coreduced-identity-types (ℑ B) (ℑ-is-coreduced _) _ _)

  induce-homotopy-on-coreduced-types :
      ∀ {A B : 𝒰₀} (f g : ℑ A → ℑ B)
      → f ∘ ℑ-unit ⇒ g ∘ ℑ-unit
      → f ⇒ g
  induce-homotopy-on-coreduced-types f g H =
      ℑ-induction (λ _ → coreduced-types-have-coreduced-identity-types _ (ℑ-is-coreduced _) _ _) H

  coreduced-types-have-a-coreduced-equivalence-proposition :
      ∀ {A B : 𝒰₀}
      → (f : ℑ A → ℑ B) → (f is-an-equivalence) is-coreduced
  coreduced-types-have-a-coreduced-equivalence-proposition {A} {B} f =
       (to-show-that (f is-an-equivalence) is-coreduced,-it-suffices-to-show-that (∑ _)
        is-coreduced-since-it-is-equivalent-by (equivalence-proposition-as-sum-type f))
        (∑-of-coreduced-types-is-coreduced
          ((ℑ B → ℑ A) × (ℑ B → ℑ A))
          (∑-of-coreduced-types-is-coreduced _ (Π-of-coreduced-types-is-coreduced.coreducedness (λ _ → ℑ _) (λ _ → ℑ-is-coreduced _)) _
            (λ i → Π-of-coreduced-types-is-coreduced.coreducedness _ (λ _ → ℑ-is-coreduced _)))
          (λ {(g , h) → (g ∘ f ⇒ id) × (id ⇒ f ∘ h)})
          (λ {(g , h) →  ∑-of-coreduced-types-is-coreduced
                         (g ∘ f ⇒ id)
                           homotopies-in-coreduced-types-are-coreduced
                         (λ _ → id ⇒ f ∘ h)
                           (λ _ → homotopies-in-coreduced-types-are-coreduced)}))

  ℑ≃-is-coreduced : ∀ {A B : 𝒰₀}
    → (ℑ A ≃ ℑ B) is-coreduced
  ℑ≃-is-coreduced {A} {B} =
    (to-show-that (ℑ A ≃ ℑ B) is-coreduced,-it-suffices-to-show-that
        (∑ λ (f : ℑ A → ℑ B) → f is-an-equivalence)
     is-coreduced-since-it-is-equivalent-by type-of-equivalences-as-sum-type)
    (This-follows-from
       (∑-of-coreduced-types-is-coreduced
         (ℑ A → ℑ B)
         (Π-of-coreduced-types-is-coreduced.coreducedness _ λ _ → ℑ-is-coreduced _)
         _is-an-equivalence
         (λ (f : ℑ A → ℑ B) → coreduced-types-have-a-coreduced-equivalence-proposition
           f)))

  naturality-of-ℑ-unit≃ :
    ∀ {A B : 𝒰₀}
    → (f : A ≃ B)
    → (a : A) → (ℑ≃ f $≃ (ℑ-unit a) ≈ ℑ-unit (f $≃ a))
  naturality-of-ℑ-unit≃ {_} {B} f = ℑ-compute-recursion (ℑ-is-coreduced B) (λ z → ℑ-unit (underlying-map-of f z))


  ×-coreduced :
    ∀ (A B : 𝒰₀)
    → (ℑ A × ℑ B) is-coreduced
  ×-coreduced A B = ∑-of-coreduced-types-is-coreduced
                  (ℑ A) (ℑ-is-coreduced A) (λ _ → ℑ B) (λ _ → ℑ-is-coreduced B)


  module ℑ-preserves-products (A B : 𝒰₀) where
    curry : ∀ {A B C : 𝒰₀} → (A × B → C) → (A → (B → C))
    curry f = λ a → (λ b → f (a , b))

    uncurry : ∀ {A B C : 𝒰₀} → (A → (B → C)) → (A × B → C)
    uncurry f (a , b) = f a b

    ψ : A → (B → ℑ(A × B))
    ψ = curry (ℑ-unit-at (A × B))

    ℑB→ℑ-A×B-is-coreduced : (ℑ B → ℑ (A × B)) is-coreduced
    ℑB→ℑ-A×B-is-coreduced =
      Π-of-coreduced-types-is-coreduced.coreducedness
        (λ _ → ℑ (A × B)) (λ _ → ℑ-is-coreduced _)

    ψ′ : A → (ℑ B → ℑ(A × B))
    ψ′ x = ℑ-recursion (ℑ-is-coreduced (A × B)) (ψ x)

    ψ′′ : ℑ A → (ℑ B → ℑ(A × B))
    ψ′′ = ℑ-recursion
           (ℑB→ℑ-A×B-is-coreduced)
           ψ′

    φ : ℑ A × ℑ B → ℑ(A × B)
    φ = uncurry ψ′′

    φ⁻¹ : ℑ(A × B) → ℑ A × ℑ B
    φ⁻¹ = ℑ-recursion (×-coreduced _ _) (ι ×→ ι)

    pair-construction :
      ∀ (x : A) (y : B)
      → φ (ℑ-unit x , ℑ-unit y) ≈ ℑ-unit (x , y)
    pair-construction x y =
       φ (ℑ-unit x , ℑ-unit y)
      ≈⟨ (λ f → f (ℑ-unit y)) ⁎
           ℑ-compute-recursion ℑB→ℑ-A×B-is-coreduced ψ′ x ⟩
       ψ′ x (ℑ-unit y)
      ≈⟨ ℑ-compute-recursion (ℑ-is-coreduced (A × B)) (ψ x) y ⟩
       ψ x y
      ≈⟨ refl ⟩
       ℑ-unit (x , y)
      ≈∎

    φ⁻¹-commutes-with-π₁ :
      ∀ (x : A × B)
      → (π₁ (φ⁻¹ (ι x)) ≈ ι (π₁ x))
    φ⁻¹-commutes-with-π₁ (a , b) =
       π₁ ⁎ ℑ-compute-recursion (×-coreduced _ _) (ι ×→ ι) (a , b)

    φ⁻¹-commutes-with-π₂ :
      ∀ (x : A × B)
      → (π₂ (φ⁻¹ (ι x)) ≈ ι (π₂ x))
    φ⁻¹-commutes-with-π₂ (a , b) =
      π₂ ⁎ ℑ-compute-recursion (×-coreduced _ _) (ι ×→ ι) (a , b)

  {-
    General modalities are not left exact but there is a
    special kind of pullback that any modality preserves.
    Let A be some type, and B a coreduced type and φ : B → ℑA.
    Then the following pullback square is preserved by ℑ:

      PB ──→ B
       |     |
       ↓     ↓
       A ──→ ℑA

    We will write B as a ∑ over a coreduced dependent type.
    So below we start with a B : ℑA → ℑ𝒰₀ and show the theorem
    for the square

      ∑B∘ι ──→ ∑B
       |       |
       ↓       ↓
       A ───→ ℑA

    As a byproduct, we will show that this is the naturality square
    for the projection PB ─→ A.
    But in fact, we will start with a dependent version close to this
    statement, i.e.

      ℑ(∑ (x : A) ↦ B(ι(x))) ≃ (∑ (x : ℑA) ↦ B(x))
  -}
  module ℑ-preserves-special-pullbacks (A : 𝒰₀) (B : ℑ A → 𝒰₀) where
    ℑB = (λ x → ℑ (B x))

    φ : ℑ (∑ (B ∘ ι)) → ∑ ℑB
    φ = ℑ-recursion
          (∑-of-coreduced-types-is-coreduced (ℑ A) (ℑ-is-coreduced _) ℑB (λ x → ℑ-is-coreduced _))
          (λ {(x , bₓ) → (ι x) , ι bₓ})

    f : ∑ (B ∘ ι) → ∑ ℑB
    f (x , bₓ) = ((ι x) , ι bₓ)

    ∑ℑB-is-universal :
      ∀ (C : 𝒰₀) (p : C is-coreduced)
      → (λ (h : ∑ ℑB → C) → h ∘ f) is-an-equivalence
    ∑ℑB-is-universal C p = proof-of-equivalency (
         (∑ ℑB → C)                        ≃⟨ dependent-curry C ⟩
         (Π λ (x : ℑ A) → (ℑB x → C))      ≃⟨ ℑ-induction-as-equivalence
                                               (λ a → Π-of-coreduced-types-is-coreduced.coreducedness
                                                 _ (λ x → p)) ⟩
         Π (λ (x : A) → (ℑB (ι x) → C))    ≃⟨ applying-equivalences-to-codomain.induced-equivalence
                                                (λ x → (ℑB (ι x) → C)) (λ x → (B (ι x) → C))
                                                (λ x → ℑ-induction-as-equivalence (λ _ → p)) ⟩
         Π (λ (x : A) → (B (ι x) → C))      ≃⟨ dependent-curry C ⁻¹≃ ⟩
         (∑ (B ∘ ι) → C)
       ≃∎)

    compute-∑ : ℑ (∑ (B ∘ ι)) ≃ ∑ ℑB
    compute-∑ = ℑ-yoneda
               f (∑-of-coreduced-types-is-coreduced (ℑ A) (ℑ-is-coreduced _) ℑB (λ x → ℑ-is-coreduced _))
               ∑ℑB-is-universal
