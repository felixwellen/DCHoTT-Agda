{-# OPTIONS --without-K #-}

module Im where 
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
  open import Univalence                     -- for now, just convenience
  open import NonAssociativeGroup

  -- Axioms for ℑ, the infinitesimal shape modality
  -- (this may also be read as axiomatizing a general lex Modality)
  -- the axioms are taken from a n-cafe post from mike shulman
  -- "internalizing the external, or the joy of codiscreteness"
  -- update: except the lexness-axioms
  -- update: Now, it is close to the definition from the HoTT-Book

  postulate
    ℑ : ∀ {i} → U i → U i
    ℑ-unit : ∀ {i} {A : U i} → A → ℑ A


  ℑ-unit-at :
    ∀ {i} → (A : U i)
    → (A → ℑ A)
  ℑ-unit-at A = ℑ-unit {_} {A}

  _is-coreduced : ∀ {i} → U i → U i
  A is-coreduced = ℑ-unit {_} {A} is-an-equivalence

  postulate
    -- ℑ is idempotent
    ℑ-is-coreduced : ∀ {i} → (A : U i) → (ℑ A) is-coreduced

    ℑ-induction :  
      ∀ {i} {A : U i} {B : ℑ A → U i}
      → (∀ (a : ℑ A) → B(a) is-coreduced)
      → ((a : A) → B(ℑ-unit a))
      → ((a : ℑ A) → B(a))
    ℑ-compute-induction :  
      ∀ {i} {A : U i} {B : ℑ A → U i}
      → (coreducedness : ∀ (a : ℑ A) → B(a) is-coreduced)
      → (f : (a : A) → B(ℑ-unit a))
      → (a : A) → (ℑ-induction coreducedness f) (ℑ-unit a) ≈ f a

    coreduced-types-have-coreduced-identity-types :
      ∀ (B : U₀) → (B is-coreduced) → (b b′ : B) 
      → ℑ-unit-at (b ≈ b′) is-an-equivalence

  Ω-of-ℑ-is-coreduced : 
    ∀ (A : U₀) (a : A)
    → (Ω (ℑ A) (ℑ-unit a)) is-coreduced
  Ω-of-ℑ-is-coreduced A a = 
    coreduced-types-have-coreduced-identity-types 
      (ℑ A) (ℑ-is-coreduced A) (ℑ-unit a) (ℑ-unit a)
                             
    -- maybe lexness or some special case
  postulate
    ℑ-commutes-with-Ω : 
      ∀ (A : U₀) (a : A)
      → ℑ-induction (λ (γ : ℑ (Ω A a)) → Ω-of-ℑ-is-coreduced A a) (λ γ → ℑ-unit ⁎ γ) is-an-equivalence


    -- mike's more concise condition for lexness, which he told me in toronto:
    ℑ-condition-for-lexness : 
      ∀ {A : U₀}
      → (ℑ A) is-contractible 
      → Π {_} {_} {A × A} (λ {(x , y) → ((ℑ (x ≈ y)) is-contractible)}) 

  -- mike's old condition for lexness
  --    ℑ-condition-for-lexness :  {A B : U₀}
  --                             → (ℑ A) is-contractible → (ℑ B) is-contractible
  --                             → ∀ (f : A → B) (b : B) → (ℑ (fiber-of f at b)) is-contractible
  --
  
  -- End Axioms


  ℑ-recursion : 
    ∀ {A B : U₀} 
    → B is-coreduced 
    → (A → B) 
    → (ℑ A → B)
  ℑ-recursion coreducedness f = ℑ-induction (λ a → coreducedness) (λ a → f a)

  ℑ-compute-recursion :
    ∀ {A B : U₀} 
    → (coreducedness : B is-coreduced) 
    → (f : A → B)
    → (a : A) → (ℑ-recursion coreducedness f) (ℑ-unit a) ≈ f a
  ℑ-compute-recursion coreducedness f = ℑ-compute-induction (λ a → coreducedness) f

  apply-ℑ-to-map :
    ∀ {A B : U₀}
    → (A → B)
    → (ℑ A → ℑ B)
  apply-ℑ-to-map {_} {B} f = ℑ-recursion (ℑ-is-coreduced B) (ℑ-unit {_} {B} ∘ f)

  apply-ℑ : ∀ {A B : U₀}
            → (A → B)
            → (ℑ A → ℑ B)
  apply-ℑ f = apply-ℑ-to-map f

  ℑ→ = apply-ℑ

  naturality-square-for-ℑ : 
    ∀ {A B : U₀}
    → (f : A → B)
    → (a : A) → (apply-ℑ-to-map f(ℑ-unit {_} {A} a) ≈ ℑ-unit {_} {B}(f a))
  naturality-square-for-ℑ {_} {B} f = ℑ-compute-recursion (ℑ-is-coreduced B) (λ z → ℑ-unit (f z)) 

  naturality-of-ℑ-unit : 
    ∀ {A B : U₀}
    → (f : A → B)
    → (a : A) → (apply-ℑ-to-map f(ℑ-unit {_} {A} a) ≈ ℑ-unit {_} {B}(f a))
  naturality-of-ℑ-unit {_} {B} f = ℑ-compute-recursion (ℑ-is-coreduced B) (λ z → ℑ-unit (f z)) 

  ℑ⇒ : ∀ {A B : U₀} {f g : A → B}
       → (f ⇒ g) → (ℑ→ f ⇒ ℑ→ g)
  ℑ⇒ H = ℑ-induction
         (λ a → coreduced-types-have-coreduced-identity-types (ℑ _) (ℑ-is-coreduced _) (ℑ→ _ a) (ℑ→ _ a))
         (λ a → naturality-square-for-ℑ _ a • ℑ-unit ⁎ (H a) • naturality-square-for-ℑ _ a ⁻¹)


  -- define coreduced connectedness
  _is-ℑ-connected :
    ∀ {A B : U₀} (f : A → B)
    → U₀ 
  _is-ℑ-connected {_} {B} f  = ∀ (b : B) → ℑ (fiber-of f at b) is-contractible


--      
--  the-preimages-of-equivalences-are-ℑ-connected =
--    {!!}

{-
  units-are-ℑ-connected :
    ∀ {A : U₀}
    → (ℑ-unit-at A) is-ℑ-connected
  units-are-ℑ-connected = {!!}
-}
  -- it is preserved under composition
--  composition-preserves-ℑ-connectedness :
--    ∀ {A B C : U₀} (f : A → B) (g : B → C)
--    → (f is-ℑ-connected) → (g is-ℑ-connected)
--    → (g ∘ f) is-ℑ-connected 
--  composition-preserves-ℑ-connectedness f g f-is-ℑ-connected g-is-ℑ-connected c =
--    {!!}



  ℑ-recursion-is-unique : 
    ∀ {A B : U₀} (f : A → B) (coreducedness : B is-coreduced)
    → (φ : ℑ A → B) → f ∼ φ ∘ ℑ-unit 
    → ℑ-recursion coreducedness f ∼ φ
  ℑ-recursion-is-unique {A} {B} f coreducedness φ φ-factors = 
    let
        factor-over-unit : (A → B) → (ℑ A → B)
        factor-over-unit = ℑ-recursion coreducedness
        factoring-is-nice : ∀ (g : ℑ A → B)
                            → factor-over-unit (g ∘ ℑ-unit) ∼ g
        factoring-is-nice g = 
          let
            true-on-contructed = ℑ-compute-recursion coreducedness (g ∘ ℑ-unit)
          in ℑ-induction
               (λ x → coreduced-types-have-coreduced-identity-types 
                        B coreducedness (factor-over-unit (g ∘ ℑ-unit) x) (g x))
               true-on-contructed 
        induced-map = ℑ-recursion coreducedness f
        both-factor-the-same-map : induced-map ∘ ℑ-unit ∼ φ ∘ ℑ-unit
        both-factor-the-same-map = compose-homotopies (ℑ-compute-recursion coreducedness f) φ-factors
    in compose-homotopies
        (reverse-homotopy (factoring-is-nice induced-map))
          (compose-homotopies
            (mapping-preserves-homotopy factor-over-unit
               both-factor-the-same-map)
               (factoring-is-nice φ))


  module ℑ-is-idempotent (E : U₀) (E-is-coreduced : E is-coreduced) where
  -- 'idempotency for ℑ' 
  -- here, we merely define the inverse to the equivalence appearing in
  -- the axiom stating that ℑA is coreduced, for all A
    
    ℑ-unit⁻¹ : ℑ E → E
    ℑ-unit⁻¹ = ℑ-recursion E-is-coreduced id

    left-invertible : ℑ-unit⁻¹ ∘ ℑ-unit ⇒ id
    left-invertible = ℑ-compute-recursion E-is-coreduced id

  cancel-one-ℑ-on :
    ∀ (A : U₀)
    → ℑ (ℑ A) → ℑ A
  cancel-one-ℑ-on A = ℑ-recursion (ℑ-is-coreduced A) id

  apply-ℑ-commutes-with-∘ : 
    ∀ {A B C : U₀}
    → (f : A → B) → (g : B → C)
    → apply-ℑ (g ∘ f) ⇒ (apply-ℑ g) ∘ (apply-ℑ f)
  apply-ℑ-commutes-with-∘ f g = 
    ℑ-recursion-is-unique 
           (ℑ-unit ∘ (g ∘ f)) 
           (ℑ-is-coreduced _) 
           (apply-ℑ g ∘ apply-ℑ f) 
           (λ a → naturality-square-for-ℑ g (f a) ⁻¹ 
                  • (λ x → apply-ℑ g x) ⁎ naturality-square-for-ℑ f a ⁻¹)

  applying-ℑ-preserves-id : ∀ (A : U₀)
                            → apply-ℑ (id {_} {A}) ⇒ id {_} {ℑ A}
  applying-ℑ-preserves-id A =
    ℑ-recursion-is-unique (ℑ-unit ∘ id {_} {A}) (ℑ-is-coreduced A) id (λ _ → refl)

  applying-ℑ-preserves-equivalences : ∀ {A B : U₀} (f : A → B)
                                      → f is-an-equivalence
                                      → (apply-ℑ f) is-an-equivalence
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

  apply-ℑ-to-the-equivalence : ∀ {A B : U₀}
                               → A ≃ B → ℑ A ≃ ℑ B
  apply-ℑ-to-the-equivalence 
    (f is-an-equivalence-because proof-of-invertibility) =
      apply-ℑ f is-an-equivalence-because
        applying-ℑ-preserves-equivalences f proof-of-invertibility


  module the-ℑ-preimages-of-equivalences-are-ℑ-connected -- not yet complete
    {A B : U₀} (f : A → B) (ℑf-is-an-equivalence : (ℑ→ f) is-an-equivalence) where

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

  types-equivalent-to-their-coreduction-are-coreduced :
    ∀ {A : U₀} (f : A ≃ ℑ A)
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


  ℑ-One-is-contractible : (ℑ One) is-contractible
  ℑ-One-is-contractible = 
    let ∗̂ = (id ∘ ℑ-unit {_} {One}) ∗
        constant-∗̂ : ∀ {A : U₀} → A → ℑ One
        constant-∗̂ = λ x → ∗̂
                                                    
        id∘ℑ-unit∼constant-∗̂ : id ∘ ℑ-unit ∼ constant-∗̂
        id∘ℑ-unit∼constant-∗̂ = λ {∗ → refl}
                                                               
        factored-trivial-map = ℑ-recursion (ℑ-is-coreduced One) (id ∘ ℑ-unit)
                                                                      
        step1 : factored-trivial-map ∼ id 
        step1 = ℑ-recursion-is-unique
              (id ∘ ℑ-unit) (ℑ-is-coreduced One) id (λ a → refl) 
                                                         
        step2 : factored-trivial-map ∼ constant-∗̂
        step2 = ℑ-recursion-is-unique (id ∘ ℑ-unit) (ℑ-is-coreduced One)
                constant-∗̂ id∘ℑ-unit∼constant-∗̂
                                                      
        step3 : id ∼ constant-∗̂
        step3 = compose-homotopies (reverse-homotopy step1) step2
                                                                                    
    in reformulate-contractibilty-as-homotopy (ℑ One) ∗̂
       step3



  -- the hott book told me the following is true:
  retracts-of-coreduced-types-are-coreduced : 
    ∀ (A E : U₀) → (E is-coreduced) 
    → (ι : A → E) (r : E → A)
    → r ∘ ι ∼ id
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
  -- (specialized to ℑ)

  module Π-of-coreduced-types-is-coreduced
    {A : U₀} (P : A → U₀)
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
                      (λ (X : U₀) → X is-coreduced)
                      (Π ⁎ fun-ext (λ (a : A) → univalence (ℑ-unit-at (P a) is-an-equivalence-because (P-is-coreduced a)) ⁻¹))
                      coreducedness′
                      

  -- from the book, thm 7.7.4
  ∑-of-coreduced-types-is-coreduced : 
    ∀ (E : U₀)
    → (E is-coreduced) → (P : E → U₀)
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

        P′ : ℑ (∑ P) → U₀
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
    ∀ (E : U₀)
    → (E is-coreduced) → (P : E → U₀)
    → ((e : E) → (P e) is-coreduced)
    → ∑ P ≃ ℑ (∑ P)
  cancel-ℑ-of-∑ E E-is-coreduced P P-is-coreduced = 
    (ℑ-unit is-an-equivalence-because 
      ∑-of-coreduced-types-is-coreduced E E-is-coreduced P P-is-coreduced) 

  canonical-pullback-of-coreduced-types-is-coreduced :
    ∀ {A B C : U₀} {f : A → C} {g : B → C}
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
    ∀ (A B : U₀)
    → (A ≃ B) → (B is-coreduced → A is-coreduced)
  to-show-that A is-coreduced,-it-suffices-to-show-that B is-coreduced-since-it-is-equivalent-by φ =
    transport _is-coreduced (univalence (φ ⁻¹≃))

  -- ∞-groups and ℑ
  module ∞-groups-and-ℑ (BG : U₀) (e : BG) where
  
    G = Ω BG e
    
    unit-commutes-with-Δ : ∀ (g h : G)
                           → (ℑ-unit ⁎ g) • (ℑ-unit ⁎ h) ⁻¹ ≈ ℑ-unit ⁎ (g • h ⁻¹)
    unit-commutes-with-Δ g h = 
                         (λ ξ → ℑ-unit ⁎ g • ξ) ⁎ application-commutes-with-inversion ℑ-unit h ⁻¹ 
                         • application-commutes-with-concatenation ℑ-unit g (h ⁻¹) ⁻¹



  module ℑ-preserves-non-associative-groups
         (X : U₀)
         (non-associative-group-structure-on-X : non-associative-group-structure-on X)
       where
     
    open non-associative-group-structure-on_ non-associative-group-structure-on-X
    ℑX = ℑ X
  
    coreduced : (ℑX × ℑX) is-coreduced
    coreduced = ∑-of-coreduced-types-is-coreduced 
                           (ℑ X) (ℑ-is-coreduced X) (λ _ → ℑ X) (λ _ → ℑ-is-coreduced X)

    curry : ∀ {A B C : U₀} → (A × B → C) → (A → (B → C))
    curry f = λ a → (λ b → f (a , b))
    
    ψ : X → (X → ℑ(X × X))
    ψ = curry (ℑ-unit-at (X × X))

    ℑX→ℑ-X×X-is-coreduced : (ℑ X → ℑ (X × X)) is-coreduced
    ℑX→ℑ-X×X-is-coreduced = Π-of-coreduced-types-is-coreduced.coreducedness (λ _ → ℑ (X × X)) (λ _ → ℑ-is-coreduced _)

    ψ′ : X → (ℑX → ℑ(X × X))
    ψ′ x = ℑ-recursion (ℑ-is-coreduced (X × X)) (ψ x)

    ψ′′ : ℑX → (ℑX → ℑ(X × X))
    ψ′′ = ℑ-recursion
           (ℑX→ℑ-X×X-is-coreduced)
           ψ′
    
    uncurry : ∀ {A B C : U₀} → (A → (B → C)) → (A × B → C)
    uncurry f (a , b) = f a b

    φ : ℑX × ℑX → ℑ(X × X)
    φ = uncurry ψ′′

    -- operations of the image H-Space
    ℑμ : ℑX × ℑX → ℑX
    ℑμ = ℑ→ μ ∘ φ 

    ℑe : ℑX
    ℑe = ℑ-unit e

    -- relations of the image H-Space

    {-

       first, get a 2-cell where the question mark is

      /───X        ℑX×ℑX←─(ℑe,1)  
      |   |          |        \
      | (e,1)        φ    ?    \
      |   ↓          ↓          \
      1  X×X ───→ ℑ(X×X)←ℑ→(e,1)─ℑX
      |   |          |          /
      |   μ         ℑ→μ        /
      |   ↓          ↓        /
      \───X ──────→ ℑX─────ℑ→1  


      this is essentially done by showing that ℑ commutes with
      constructing pairs
    -}

    ℑ-commutes-with-pair-construction :
      ∀ (x x′ : X)
      → φ (ℑ-unit x , ℑ-unit x′) ≈ ℑ-unit (x , x′) 
    ℑ-commutes-with-pair-construction x x′ =
       φ (ℑ-unit x , ℑ-unit x′)
      ≈⟨ (λ f → f (ℑ-unit x′)) ⁎
           ℑ-compute-recursion ℑX→ℑ-X×X-is-coreduced ψ′ x ⟩
       ψ′ x (ℑ-unit x′)
      ≈⟨ ℑ-compute-recursion (ℑ-is-coreduced (X × X)) (ψ x) x′ ⟩
       ψ x x′
      ≈⟨ refl ⟩
       ℑ-unit (x , x′)
      ≈∎

    ℑright-neutral′ : ∀ (x : X) → ℑμ (ℑ-unit x , ℑe) ≈ ℑ-unit x
    ℑright-neutral′ x = ℑμ (ℑ-unit x , ℑe)
                    ≈⟨ refl ⟩
                     ℑ→ μ (φ (ℑ-unit x , ℑe))
                    ≈⟨ ℑ→ μ ⁎ ℑ-commutes-with-pair-construction x e ⟩ 
                     ℑ→ μ (ℑ-unit (x , e))
                    ≈⟨ naturality-of-ℑ-unit μ (x , e) ⟩
                     ℑ-unit (μ (x , e))
                    ≈⟨ ℑ-unit ⁎ right-neutral x ⟩
                     ℑ-unit x
                    ≈∎

    ℑright-neutral : ∀ (x : ℑX) → ℑμ (x , ℑe) ≈ x
    ℑright-neutral = ℑ-induction
                       (λ (x : ℑX) →
                          coreduced-types-have-coreduced-identity-types ℑX (ℑ-is-coreduced _)
                          (ℑμ (x , ℑe)) x)
                       ℑright-neutral′


    ℑleft-neutral′ : ∀ (x : X) → ℑμ (ℑe , ℑ-unit x ) ≈ ℑ-unit x
    ℑleft-neutral′ x = ℑμ (ℑe , ℑ-unit x )
                    ≈⟨ refl ⟩
                     ℑ→ μ (φ (ℑe , ℑ-unit x ))
                    ≈⟨ ℑ→ μ ⁎ ℑ-commutes-with-pair-construction e x ⟩ 
                     ℑ→ μ (ℑ-unit (e , x))
                    ≈⟨ naturality-of-ℑ-unit μ (e , x) ⟩
                     ℑ-unit (μ (e , x))
                    ≈⟨ ℑ-unit ⁎ left-neutral x ⟩
                     ℑ-unit x
                    ≈∎

    ℑleft-neutral : ∀ (x : ℑX) → ℑμ (ℑe , x) ≈ x
    ℑleft-neutral = ℑ-induction
                       (λ (x : ℑX) →
                          coreduced-types-have-coreduced-identity-types ℑX (ℑ-is-coreduced _)
                          (ℑμ (ℑe , x)) x)
                       ℑleft-neutral′


    {-

      ℑ preserves inversion

    -}

    homotopies-in-coreduced-types-are-coreduced :
      ∀ {A B : U₀} {f g : ℑ A → ℑ B} → (f ⇒ g) is-coreduced
    homotopies-in-coreduced-types-are-coreduced {A} {B} {_} {_} =
      Π-of-coreduced-types-is-coreduced.coreducedness _
        (λ (a : ℑ A) →
          coreduced-types-have-coreduced-identity-types (ℑ B) (ℑ-is-coreduced _) _ _)

    coreduced-types-have-a-coreduced-equivalence-proposition :
      ∀ {A B : U₀}
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

    ℑ-of-curried-equivalence :
      ∀ (x₀ : X)
      → ℑ→ (λ (x : X) → μ (x , x₀)) ⇒ λ (x : ℑX) → ℑμ (x , ℑ-unit x₀)
    ℑ-of-curried-equivalence x₀ x =
      ℑ→ (λ x₁ → μ (x₁ , x₀)) x
     ≈⟨ {!!} ⟩
       {!!}
     ≈⟨ {!!} ⟩
      ℑμ (x , ℑ-unit x₀)
     ≈∎

    ℑleft-invertible′ :
      ∀ (x₀ : X) → (λ (x : ℑX) → ℑμ (x , ℑ-unit x₀)) is-an-equivalence
    ℑleft-invertible′ x₀ = {!applying-ℑ-preserves-equivalences (λ (x : X) → μ (x , x₀)) (left-invertible x₀) !}
