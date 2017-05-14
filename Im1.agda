{-# OPTIONS --without-K #-}

module Im1 where 
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Contractibility
  open import Equivalences
  open import CommonEquivalences
  open import InfinityGroups
  open import FunctionExtensionality
  open import Pullback
  open import PullbackSquare
  open import Fiber
  open import Language
  open import Univalence
  open import Im

  -- Axioms for ℑ₁, the first-order infinitesimal shape modality
  -- (this may also be read as axiomatizing a general modality with one exception, see ↓)
  -- in addition to modality-axioms, we require the ℑ₁-modal to contain the ℑ-modal types
  -- the contents of this file are almost completely copied from 'Im.agda' 

  postulate
    ℑ₁ : ∀ {i} → U i → U i
    ℑ₁-unit : ∀ {i} {A : U i} → A → ℑ₁ A


  ℑ₁-unit-at :
    ∀ {i} → (A : U i)
    → (A → ℑ₁ A)
  ℑ₁-unit-at A = ℑ₁-unit {_} {A}

  _is-1-coreduced : ∀ {i} → U i → U i
  A is-1-coreduced = ℑ₁-unit {_} {A} is-an-equivalence


  postulate
    -- ℑ is a 'sub modality'
    coreduced-types-are-1-coreduced :
      ∀ {A : U₀} → A is-coreduced → A is-1-coreduced
      
    -- ℑ₁ is idempotent
    ℑ₁-is-1-coreduced : ∀ {i} → (A : U i) → (ℑ₁ A) is-1-coreduced

    ℑ₁-induction :  
      ∀ {A : U₀} {B : ℑ₁ A → U₀}
      → (∀ (a : ℑ₁ A) → B(a) is-1-coreduced)
      → ((a : A) → B(ℑ₁-unit a))
      → ((a : ℑ₁ A) → B(a))
    ℑ₁-compute-induction :  
      ∀ {A : U₀} {B : ℑ₁ A → U₀}
      → (1-coreducedness : ∀ (a : ℑ₁ A) → B(a) is-1-coreduced)
      → (f : (a : A) → B(ℑ₁-unit a))
      → (a : A) → (ℑ₁-induction 1-coreducedness f) (ℑ₁-unit a) ≈ f a

    1-coreduced-types-have-1-coreduced-identity-types :
      ∀ (B : U₀) → (B is-1-coreduced) → (b b′ : B) 
      → (b ≈ b′) is-1-coreduced

  
  -- End Axioms


  ℑ₁-recursion : 
    ∀ {A B : U₀} 
    → B is-1-coreduced 
    → (A → B) 
    → (ℑ₁ A → B)
  ℑ₁-recursion 1-coreducedness f = ℑ₁-induction (λ a → 1-coreducedness) (λ a → f a)

  ℑ₁-compute-recursion :
    ∀ {A B : U₀} 
    → (1-coreducedness : B is-1-coreduced) 
    → (f : A → B)
    → (a : A) → (ℑ₁-recursion 1-coreducedness f) (ℑ₁-unit a) ≈ f a
  ℑ₁-compute-recursion 1-coreducedness f = ℑ₁-compute-induction (λ a → 1-coreducedness) f

  apply-ℑ₁-to-map :
    ∀ {A B : U₀}
    → (A → B)
    → (ℑ₁ A → ℑ₁ B)
  apply-ℑ₁-to-map {_} {B} f = ℑ₁-recursion (ℑ₁-is-1-coreduced B) (ℑ₁-unit {_} {B} ∘ f)

  apply-ℑ₁ : ∀ {A B : U₀}
            → (A → B)
            → (ℑ₁ A → ℑ₁ B)
  apply-ℑ₁ f = apply-ℑ₁-to-map f

  ℑ₁→ = apply-ℑ₁

  naturality-square-for-ℑ₁ : 
    ∀ {A B : U₀}
    → (f : A → B)
    → (a : A) → (apply-ℑ₁-to-map f(ℑ₁-unit {_} {A} a) ≈ ℑ₁-unit {_} {B}(f a))
  naturality-square-for-ℑ₁ {_} {B} f = ℑ₁-compute-recursion (ℑ₁-is-1-coreduced B) (λ z → ℑ₁-unit (f z)) 

  naturality-of-ℑ₁-unit : 
    ∀ {A B : U₀}
    → (f : A → B)
    → (a : A) → (apply-ℑ₁-to-map f(ℑ₁-unit {_} {A} a) ≈ ℑ₁-unit {_} {B}(f a))
  naturality-of-ℑ₁-unit {_} {B} f = ℑ₁-compute-recursion (ℑ₁-is-1-coreduced B) (λ z → ℑ₁-unit (f z)) 

  ℑ₁⇒ : ∀ {A B : U₀} {f g : A → B}
       → (f ⇒ g) → (ℑ₁→ f ⇒ ℑ₁→ g)
  ℑ₁⇒ H = ℑ₁-induction
         (λ a → 1-coreduced-types-have-1-coreduced-identity-types (ℑ₁ _) (ℑ₁-is-1-coreduced _) (ℑ₁→ _ a) (ℑ₁→ _ a))
         (λ a → naturality-square-for-ℑ₁ _ a • ℑ₁-unit ⁎ (H a) • naturality-square-for-ℑ₁ _ a ⁻¹)


  ℑ₁⁎_⁎_ :
    ∀ {A B : U₀} {x y : A}
    → (f : A → B)
    → ((ℑ₁-unit x ≈ ℑ₁-unit y) → (ℑ₁-unit (f(x)) ≈ ℑ₁-unit (f(y))))
  ℑ₁⁎ f ⁎ γ = naturality-square-for-ℑ₁ f _ ⁻¹ • ℑ₁→ f ⁎ γ • naturality-square-for-ℑ₁ f _


  -- define 1-coreduced connectedness
  _is-ℑ₁-connected :
    ∀ {A B : U₀} (f : A → B)
    → U₀ 
  _is-ℑ₁-connected {_} {B} f  = ∀ (b : B) → ℑ₁ (fiber-of f at b) is-contractible


  ℑ₁-recursion-is-unique : 
    ∀ {A B : U₀} (f : A → B) (1-coreducedness : B is-1-coreduced)
    → (φ : ℑ₁ A → B) → f ⇒ φ ∘ ℑ₁-unit 
    → ℑ₁-recursion 1-coreducedness f ⇒ φ
  ℑ₁-recursion-is-unique {A} {B} f 1-coreducedness φ φ-factors = 
    let
        factor-over-unit : (A → B) → (ℑ₁ A → B)
        factor-over-unit = ℑ₁-recursion 1-coreducedness
        factoring-is-nice : ∀ (g : ℑ₁ A → B)
                            → factor-over-unit (g ∘ ℑ₁-unit) ⇒ g
        factoring-is-nice g = 
          let
            true-on-constructed = ℑ₁-compute-recursion 1-coreducedness (g ∘ ℑ₁-unit)
          in ℑ₁-induction
               (λ x → 1-coreduced-types-have-1-coreduced-identity-types 
                        B 1-coreducedness (factor-over-unit (g ∘ ℑ₁-unit) x) (g x))
               true-on-constructed 
        induced-map = ℑ₁-recursion 1-coreducedness f
        both-factor-the-same-map : induced-map ∘ ℑ₁-unit ⇒ φ ∘ ℑ₁-unit
        both-factor-the-same-map = compose-homotopies (ℑ₁-compute-recursion 1-coreducedness f) φ-factors
    in compose-homotopies
        (reverse-homotopy (factoring-is-nice induced-map))
        (compose-homotopies
           (mapping-preserves-homotopy factor-over-unit both-factor-the-same-map)
           (factoring-is-nice φ))


  module ℑ₁-is-idempotent (E : U₀) (E-is-1-coreduced : E is-1-coreduced) where
  -- 'idempotency for ℑ₁' 
  -- here, we merely define the inverse to the equivalence appearing in
  -- the axiom stating that ℑ₁A is 1-coreduced, for all A
    
    ℑ₁-unit⁻¹ : ℑ₁ E → E
    ℑ₁-unit⁻¹ = ℑ₁-recursion E-is-1-coreduced id

    left-invertible : ℑ₁-unit⁻¹ ∘ ℑ₁-unit ⇒ id
    left-invertible = ℑ₁-compute-recursion E-is-1-coreduced id

  cancel-one-ℑ₁-on :
    ∀ (A : U₀)
    → ℑ₁ (ℑ₁ A) → ℑ₁ A
  cancel-one-ℑ₁-on A = ℑ₁-recursion (ℑ₁-is-1-coreduced A) id

  apply-ℑ₁-commutes-with-∘ : 
    ∀ {A B C : U₀}
    → (f : A → B) → (g : B → C)
    → apply-ℑ₁ (g ∘ f) ⇒ (apply-ℑ₁ g) ∘ (apply-ℑ₁ f)
  apply-ℑ₁-commutes-with-∘ f g = 
    ℑ₁-recursion-is-unique 
           (ℑ₁-unit ∘ (g ∘ f)) 
           (ℑ₁-is-1-coreduced _) 
           (apply-ℑ₁ g ∘ apply-ℑ₁ f) 
           (λ a → naturality-square-for-ℑ₁ g (f a) ⁻¹ 
                  • (λ x → apply-ℑ₁ g x) ⁎ naturality-square-for-ℑ₁ f a ⁻¹)

  applying-ℑ₁-preserves-id : ∀ (A : U₀)
                            → apply-ℑ₁ (id {_} {A}) ⇒ id {_} {ℑ₁ A}
  applying-ℑ₁-preserves-id A =
    ℑ₁-recursion-is-unique (ℑ₁-unit ∘ id {_} {A}) (ℑ₁-is-1-coreduced A) id (λ _ → refl)

  applying-ℑ₁-preserves-equivalences : ∀ {A B : U₀} (f : A → B)
                                      → f is-an-equivalence
                                      → (apply-ℑ₁ f) is-an-equivalence
  applying-ℑ₁-preserves-equivalences f witness =
    let ℑ₁f = apply-ℑ₁ f
        l = (_is-an-equivalence.left-inverse witness)
        r = (_is-an-equivalence.right-inverse witness)
        ℑ₁l = apply-ℑ₁ l
        ℑ₁r = apply-ℑ₁ r

        unit : ℑ₁l ∘ ℑ₁f ∼ id 
        unit = compose-homotopies (reverse-homotopy (apply-ℑ₁-commutes-with-∘ f l))
                   (ℑ₁-recursion-is-unique (ℑ₁-unit ∘ (l ∘ f)) (ℑ₁-is-1-coreduced _) id
                    (_is-an-equivalence.unit witness right-whisker ℑ₁-unit))
        
        counit : id ∼ ℑ₁f ∘ ℑ₁r
        counit = compose-homotopies 
                   (reverse-homotopy (ℑ₁-recursion-is-unique (ℑ₁-unit ∘ (f ∘ r)) (ℑ₁-is-1-coreduced _) id
                    ((reverse-homotopy (_is-an-equivalence.counit witness)) right-whisker ℑ₁-unit)))
                   (apply-ℑ₁-commutes-with-∘ r f)

    in has-left-inverse 
         ℑ₁l by unit 
       and-right-inverse 
         ℑ₁r by counit

  apply-ℑ₁-to-the-equivalence : ∀ {A B : U₀}
                               → A ≃ B → ℑ₁ A ≃ ℑ₁ B
  apply-ℑ₁-to-the-equivalence 
    (f is-an-equivalence-because proof-of-invertibility) =
      apply-ℑ₁ f is-an-equivalence-because
        applying-ℑ₁-preserves-equivalences f proof-of-invertibility


  module the-ℑ₁-preimages-of-equivalences-are-ℑ₁-connected -- not yet complete
    {A B : U₀} (f : A → B) (ℑ₁f-is-an-equivalence : (ℑ₁→ f) is-an-equivalence) where

    ℑ₁f = ℑ₁→ f
    
    fiber-inclusion-at : ∀ (b : B) → fiber-of f at b → A
    fiber-inclusion-at b (a is-in-the-fiber-by γ) = a

    fiber-inclusion-composes-to-constant-map :
      ∀ (b : B) → f ∘ (fiber-inclusion-at b) ⇒ (λ _ → b)
    fiber-inclusion-composes-to-constant-map b (a is-in-the-fiber-by γ) = γ

    the-image-factors-over-the-point :
      ∀ (b : B)
      → ℑ₁f ∘ (ℑ₁→ (fiber-inclusion-at b)) ⇒ ℑ₁→ (λ _ → b)
    the-image-factors-over-the-point b = 
      (apply-ℑ₁-commutes-with-∘ (fiber-inclusion-at b) f ⁻¹⇒) •⇒ (ℑ₁⇒ (fiber-inclusion-composes-to-constant-map b))
{-    
    conclusion : f is-ℑ₁-connected
    conclusion = {!!}
-}

  types-equivalent-to-their-1-coreduction-are-1-coreduced :
    ∀ {A : U₀} (f : A ≃ ℑ₁ A)
    → ℑ₁-unit-at A is-an-equivalence
  types-equivalent-to-their-1-coreduction-are-1-coreduced {A} f =
    let f⁻¹-as-map = underlying-map-of (f ⁻¹≃)
        f-as-map = underlying-map-of f
        ℑ₁f⁻¹ = ℑ₁→ f⁻¹-as-map
        ℑ₁f = ℑ₁→ f-as-map
        the-composition = ℑ₁f⁻¹ ∘ (ℑ₁-unit {_} {ℑ₁ A} ∘ f-as-map)
        the-composition-is-an-equivalence : the-composition is-an-equivalence
        the-composition-is-an-equivalence = proof-of-equivalency
                                              (apply-ℑ₁-to-the-equivalence (f ⁻¹≃) ∘≃
                                               (ℑ₁-unit is-an-equivalence-because (ℑ₁-is-1-coreduced _)) ∘≃ f)

        step1 : the-composition ∼ ℑ₁f⁻¹ ∘ (ℑ₁f ∘ ℑ₁-unit-at A)
        step1 a = (λ x → ℑ₁f⁻¹ x) ⁎ naturality-square-for-ℑ₁ f-as-map a ⁻¹

        step2 : ℑ₁f⁻¹ ∘ (ℑ₁f ∘ ℑ₁-unit-at A) ∼ ℑ₁-unit-at A
        step2 a = _is-an-equivalence.unit
                    (proof-of-equivalency (apply-ℑ₁-to-the-equivalence f))
                    (ℑ₁-unit a)

    in  equivalences-are-preserved-by-homotopy the-composition (ℑ₁-unit-at A)
          the-composition-is-an-equivalence (compose-homotopies step1 step2)


  ℑ₁-One-is-contractible : (ℑ₁ One) is-contractible
  ℑ₁-One-is-contractible = 
    let ∗̂ = (id ∘ ℑ₁-unit {_} {One}) ∗
        constant-∗̂ : ∀ {A : U₀} → A → ℑ₁ One
        constant-∗̂ = λ x → ∗̂
                                                    
        id∘ℑ₁-unit∼constant-∗̂ : id ∘ ℑ₁-unit ∼ constant-∗̂
        id∘ℑ₁-unit∼constant-∗̂ = λ {∗ → refl}
                                                               
        factored-trivial-map = ℑ₁-recursion (ℑ₁-is-1-coreduced One) (id ∘ ℑ₁-unit)
                                                                      
        step1 : factored-trivial-map ∼ id 
        step1 = ℑ₁-recursion-is-unique
              (id ∘ ℑ₁-unit) (ℑ₁-is-1-coreduced One) id (λ a → refl) 
                                                         
        step2 : factored-trivial-map ∼ constant-∗̂
        step2 = ℑ₁-recursion-is-unique (id ∘ ℑ₁-unit) (ℑ₁-is-1-coreduced One)
                constant-∗̂ id∘ℑ₁-unit∼constant-∗̂
                                                      
        step3 : id ∼ constant-∗̂
        step3 = compose-homotopies (reverse-homotopy step1) step2
                                                                                    
    in reformulate-contractibilty-as-homotopy (ℑ₁ One) ∗̂
       step3



  -- the hott book told me the following is true:
  retracts-of-1-coreduced-types-are-1-coreduced : 
    ∀ (A E : U₀) → (E is-1-coreduced) 
    → (ι : A → E) (r : E → A)
    → r ∘ ι ∼ id
    → (ℑ₁-unit-at A) is-an-equivalence
  -- and tobi explained a proof to me:
  retracts-of-1-coreduced-types-are-1-coreduced A E E-is-1-coreduced ι r R =
    let 
      ℑ₁-unit-E = ℑ₁-unit is-an-equivalence-because E-is-1-coreduced
      l-inverse′ = left-inverse-of-the-equivalence ℑ₁-unit-E
      r-inverse′ = right-inverse-of-the-equivalence ℑ₁-unit-E
      unit′ = unit-of-the-equivalence ℑ₁-unit-E
      counit′ = counit-of-the-equivalence ℑ₁-unit-E
      ℑ₁ι = apply-ℑ₁ ι
      ℑ₁r = apply-ℑ₁ r
      ℑ₁R = compose-homotopies (reverse-homotopy (apply-ℑ₁-commutes-with-∘ ι r))
                   (ℑ₁-recursion-is-unique (ℑ₁-unit ∘ (r ∘ ι)) (ℑ₁-is-1-coreduced _) id
                    (R right-whisker ℑ₁-unit))
      -- left and right inverses to ℑ₁-unit {A}
      l-inverse = r ∘ l-inverse′ ∘ ℑ₁ι
      r-inverse = r ∘ r-inverse′ ∘ ℑ₁ι
    in has-left-inverse l-inverse by
         (λ a → (λ x → r (l-inverse′ x)) ⁎ naturality-square-for-ℑ₁ ι a
           • ((λ x → r x) ⁎ unit′ (ι a) • R a)) 
       and-right-inverse r-inverse by
         (λ â → ℑ₁R â ⁻¹ • ((λ x → ℑ₁r x) ⁎ counit′ (ℑ₁ι â)
           • naturality-square-for-ℑ₁ r (r-inverse′ (ℑ₁ι â))))

  -- from the book "7.7 Modalities"
  -- (specialized to ℑ₁)

  module Π-of-1-coreduced-types-is-1-coreduced
    {A : U₀} (P : A → U₀)
    (P-is-1-coreduced : (a : A) → (P a) is-1-coreduced) where
    
    inverse : ℑ₁(Π(λ a → ℑ₁(P a))) → Π(λ a → ℑ₁(P a))
    inverse f̂ a = 
                  let ℑ₁πₐ : ℑ₁(Π(λ a → ℑ₁(P a))) → ℑ₁(P a)
                      ℑ₁πₐ = (ℑ₁-is-idempotent.ℑ₁-unit⁻¹ (ℑ₁ (P a)) (ℑ₁-is-1-coreduced (P a))) 
                                  ∘ apply-ℑ₁-to-map (π-Π a)
                  in ℑ₁πₐ f̂


    1-coreducedness′ : Π(λ a → ℑ₁(P a)) is-1-coreduced
    1-coreducedness′ = retracts-of-1-coreduced-types-are-1-coreduced 
               (Π (λ a → ℑ₁ (P a))) (ℑ₁ (Π (λ a → ℑ₁ (P a)))) (ℑ₁-is-1-coreduced (Π(λ a → ℑ₁ (P a))))
               ℑ₁-unit inverse (λ f →
                                   fun-ext
                                   (λ a →
                                      ℑ₁-is-idempotent.ℑ₁-unit⁻¹ (ℑ₁ (P a)) (ℑ₁-is-1-coreduced (P a)) ⁎
                                      naturality-square-for-ℑ₁ (π-Π a) f
                                      • ℑ₁-is-idempotent.left-invertible (ℑ₁ (P a)) (ℑ₁-is-1-coreduced (P a)) (f a)))
    
    1-coreducedness : Π(λ a → P a) is-1-coreduced
    1-coreducedness = transport
                      (λ (X : U₀) → X is-1-coreduced)
                      (Π ⁎ fun-ext (λ (a : A) → univalence (ℑ₁-unit-at (P a) is-an-equivalence-because (P-is-1-coreduced a)) ⁻¹))
                      1-coreducedness′
                      

  -- from the book, thm 7.7.4
  ∑-of-1-coreduced-types-is-1-coreduced : 
    ∀ (E : U₀)
    → (E is-1-coreduced) → (P : E → U₀)
    → ((e : E) → (P e) is-1-coreduced)
    → (∑ P) is-1-coreduced
  ∑-of-1-coreduced-types-is-1-coreduced E E-is-1-coreduced P P-is-1-coreduced =
    let 
        ℑ₁π : ℑ₁(∑ P) → ℑ₁ E
        ℑ₁π = apply-ℑ₁-to-map (λ {(e , _) → e})

        ℑ₁-unit-E = ℑ₁-unit is-an-equivalence-because E-is-1-coreduced
        ℑ₁-unit-E⁻¹ = ℑ₁-unit-E ⁻¹≃

        π : ∑ P → E
        π = λ {(e , _) → e}

        π′ : ℑ₁ (∑ P) → E
        π′ = underlying-map-of ℑ₁-unit-E⁻¹ ∘ ℑ₁π

        π-is-compatible-to-π′ : π ∼ π′ ∘ ℑ₁-unit
        π-is-compatible-to-π′ x = unit-of-the-equivalence ℑ₁-unit-E (π x) ⁻¹ 
                                  • underlying-map-of ℑ₁-unit-E⁻¹ ⁎ naturality-square-for-ℑ₁ π x ⁻¹

        P′ : ℑ₁ (∑ P) → U₀
        P′ p̂ = P (π′ p̂)

        -- construct a section of the bundle '∑ P → ℑ₁ ∑ P'
        -- (which will expose '∑ P' as a retract of 'ℑ₁ ∑ P')
        section-on-ℑ₁-image : (x : ∑ P) → P (π′(ℑ₁-unit x)) 
        section-on-ℑ₁-image = λ { (e , p) → transport P (π-is-compatible-to-π′ (e , p)) p }
        section : (p̂ : ℑ₁ (∑ P)) → P′ p̂
        section = ℑ₁-induction (λ p̂ → P-is-1-coreduced (π′ p̂)) section-on-ℑ₁-image
          
        r : ℑ₁ (∑ P) → ∑ P
        r x = ((π′ x) , (section x))

        calculate1 : ∀ (x : ∑ P) → r(ℑ₁-unit x) ≈ ((π′ (ℑ₁-unit x)) , (section-on-ℑ₁-image x))
        calculate1 x = (λ z → (π′ (ℑ₁-unit x) , z)) ⁎
                        ℑ₁-compute-induction (λ p̂ → P-is-1-coreduced (π′ p̂)) section-on-ℑ₁-image
                        x
        π₂ : (x : ∑ P) → P (π x) 
        π₂ = λ {(_ , p) → p}
        calculate2 : ∀ (x : ∑ P)
                     → in-the-type (∑ P) we-have-an-equality
                       ((π′ (ℑ₁-unit x)) , (section-on-ℑ₁-image x)) ≈ ((π x) , (π₂ x))
        calculate2 x =
          let γ = π-is-compatible-to-π′ x
          in construct-path-in-∑ (π x) (π′ (ℑ₁-unit x)) (π₂ x)
               (section-on-ℑ₁-image x) γ refl
               ⁻¹
        ℑ₁∑P-is-a-retract : r ∘ ℑ₁-unit-at (∑ P) ∼ id
        ℑ₁∑P-is-a-retract = compose-homotopies calculate1 calculate2
    in retracts-of-1-coreduced-types-are-1-coreduced (∑ P) (ℑ₁ (∑ P)) (ℑ₁-is-1-coreduced _)
         ℑ₁-unit r ℑ₁∑P-is-a-retract



  cancel-ℑ₁-of-∑ : 
    ∀ (E : U₀)
    → (E is-1-coreduced) → (P : E → U₀)
    → ((e : E) → (P e) is-1-coreduced)
    → ∑ P ≃ ℑ₁ (∑ P)
  cancel-ℑ₁-of-∑ E E-is-1-coreduced P P-is-1-coreduced = 
    (ℑ₁-unit is-an-equivalence-because 
      ∑-of-1-coreduced-types-is-1-coreduced E E-is-1-coreduced P P-is-1-coreduced) 

  canonical-pullback-of-1-coreduced-types-is-1-coreduced :
    ∀ {A B C : U₀} {f : A → C} {g : B → C}
    → pullback (ℑ₁→ f) (ℑ₁→ g) is-1-coreduced
  canonical-pullback-of-1-coreduced-types-is-1-coreduced {A} {B} {C} {f} {g} = 
    let
      ℑ₁A×ℑ₁B-is-1-coreduced = ∑-of-1-coreduced-types-is-1-coreduced 
                           (ℑ₁ A) (ℑ₁-is-1-coreduced A) (λ _ → ℑ₁ B) (λ _ → ℑ₁-is-1-coreduced B)
    in types-equivalent-to-their-1-coreduction-are-1-coreduced 
          ( pullback (ℑ₁→ f) (ℑ₁→ g) 
           ≃⟨ simple-reformulation.as-sum (ℑ₁→ f) (ℑ₁→ g) ⟩ 
            ∑ (simple-reformulation.fibration (ℑ₁→ f) (ℑ₁→ g)) 
           ≃⟨ cancel-ℑ₁-of-∑ (ℑ₁ A × ℑ₁ B) 
                            (ℑ₁A×ℑ₁B-is-1-coreduced) 
                            (λ { (á , b́) → (ℑ₁→ f) á ≈ (ℑ₁→ g) b́ }) 
                            ((λ { (á , b́) → 1-coreduced-types-have-1-coreduced-identity-types (ℑ₁ C) (ℑ₁-is-1-coreduced C) _ _ })) ⟩ 
            ℑ₁ (∑ (simple-reformulation.fibration (ℑ₁→ f) (ℑ₁→ g)))
           ≃⟨ (apply-ℑ₁-to-the-equivalence (simple-reformulation.as-sum (ℑ₁→ f) (ℑ₁→ g))) ⁻¹≃ ⟩ 
            ℑ₁ (pullback (ℑ₁→ f) (ℑ₁→ g)) 
           ≃∎)


  to-show-that_is-1-coreduced,-it-suffices-to-show-that_is-1-coreduced-since-it-is-equivalent-by_ :
    ∀ (A B : U₀)
    → (A ≃ B) → (B is-1-coreduced → A is-1-coreduced)
  to-show-that A is-1-coreduced,-it-suffices-to-show-that B is-1-coreduced-since-it-is-equivalent-by φ =
    transport _is-1-coreduced (univalence (φ ⁻¹≃))

     
