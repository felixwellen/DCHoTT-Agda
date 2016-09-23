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
  open import Language
    
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

    -- dependent inverse to the above / 'induction'
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

    -- the following means, coreduced types have coreduced identity types
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



  -- define coreduced connectedness (also: ℑ-connectedness)
  _is-ℑ-connected : 
    ∀ {A B : U₀} (f : A → B) → U₀ 
  _is-ℑ-connected {_} {B} f  = ∀ (b : B) → ℑ(fiber-of f at b) is-contractible
  

{-  units-are-ℑ-connected :
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
  -- idempotency for ℑ 
  -- this corresponds to the classic statement, 
  -- that given an adjunction L -| R, (L=ℑ) 
  -- the unit is an isomorphism on objects R(a) (=the coreduced objects).
  -- (this is proven in borceux, handbook I, p. 114)
    
    -- ℑ-unit is an equivalence on coreduced types
    ℑ-unit⁻¹ : ℑ E → E
    ℑ-unit⁻¹ = ℑ-recursion E-is-coreduced id

    left-invertible : ℑ-unit⁻¹ ∘ ℑ-unit ∼ id
    left-invertible = ℑ-compute-recursion E-is-coreduced id


  apply-ℑ-commutes-with-∘ : 
    ∀ {A B C : U₀}
    → (f : A → B) → (g : B → C)
    → apply-ℑ (g ∘ f) ∼ (apply-ℑ g) ∘ (apply-ℑ f)
  apply-ℑ-commutes-with-∘ f g = 
    ℑ-recursion-is-unique 
           (ℑ-unit ∘ (g ∘ f)) 
           (ℑ-is-coreduced _) 
           (apply-ℑ g ∘ apply-ℑ f) 
           (λ a → naturality-square-for-ℑ g (f a) ⁻¹ 
                  • (λ x → apply-ℑ g x) ⁎ naturality-square-for-ℑ f a ⁻¹)

  applying-ℑ-preserves-id : ∀ (A : U₀)
                            → apply-ℑ (id {_} {A}) ∼ id {_} {ℑ A}
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

  types-equivalent-to-their-coreduction-are-coreduced :
    ∀ (A : U₀) (f : A ≃ ℑ A)
    → ℑ-unit-at A is-an-equivalence
  types-equivalent-to-their-coreduction-are-coreduced A f =
    let f⁻¹-as-map = underlying-map-of (f ⁻¹≃)
        f-as-map = underlying-map-of f
        ℑf⁻¹ = apply-ℑ f⁻¹-as-map
        ℑf = apply-ℑ f-as-map
        the-composition = ℑf⁻¹ ∘ (ℑ-unit {_} {ℑ A} ∘ f-as-map)
        the-composition-is-an-equivalence : the-composition is-an-equivalence
        the-composition-is-an-equivalence = _≃_.proof-of-invertibility
                                              (apply-ℑ-to-the-equivalence (f ⁻¹≃) ∘≃
                                               (ℑ-unit is-an-equivalence-because (ℑ-is-coreduced _)) ∘≃ f)

        step1 : the-composition ∼ ℑf⁻¹ ∘ (ℑf ∘ ℑ-unit-at A)
        step1 a = (λ x → ℑf⁻¹ x) ⁎ naturality-square-for-ℑ f-as-map a ⁻¹

        step2 : ℑf⁻¹ ∘ (ℑf ∘ ℑ-unit-at A) ∼ ℑ-unit-at A
        step2 a = _is-an-equivalence.unit
                    (_≃_.proof-of-invertibility (apply-ℑ-to-the-equivalence f))
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

  module Π-of-coreduced-types-is-coreduced {A : U₀} (P : A → U₀) where
    inverse : ℑ(Π(λ a → ℑ(P a))) → Π(λ a → ℑ(P a))
    inverse f̂ a = 
                  let ℑπₐ : ℑ(Π(λ a → ℑ(P a))) → ℑ(P a)
                      ℑπₐ = (ℑ-is-idempotent.ℑ-unit⁻¹ (ℑ (P a)) (ℑ-is-coreduced (P a))) 
                                  ∘ apply-ℑ-to-map (π-Π a)
                  in ℑπₐ f̂


    coreducedness : ℑ-unit-at (Π(λ a → ℑ(P a))) is-an-equivalence
    coreducedness = retracts-of-coreduced-types-are-coreduced 
               (Π (λ a → ℑ (P a))) (ℑ (Π (λ a → ℑ (P a)))) (ℑ-is-coreduced (Π(λ a → ℑ (P a))))
               ℑ-unit inverse (λ f →
                                   fun-ext
                                   (λ a →
                                      ℑ-is-idempotent.ℑ-unit⁻¹ (ℑ (P a)) (ℑ-is-coreduced (P a)) ⁎
                                      naturality-square-for-ℑ (π-Π a) f
                                      • ℑ-is-idempotent.left-invertible (ℑ (P a)) (ℑ-is-coreduced (P a)) (f a)))
                                                                                                

  -- from the book, thm 7.7.4
  ∑-of-coreduced-types-is-coreduced : ∀ (E : U₀)
                              → (E is-coreduced) → (P : E → U₀)
                              → ((e : E) → (P e) is-coreduced)
                              → ℑ-unit-at (∑ P) is-an-equivalence
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


--  morphisms-of-coreduced-types-have-coreduced-fibers :
--    ∀ {A B : U₀} → (A is-coreduced) → (B is-coreduced)
--    → (f : A → B) 
--    → (b : B) → (fiber-of f at b) is-coreduced
--  morphisms-of-coreduced-types-have-coreduced-fibers A-is-coreduced B-is-coreduced f b = {!!}

  -- ∞-groups and ℑ
  module ∞-groups-and-ℑ (BG : U₀) (e : BG) where
  
    G = Ω BG e
    
    unit-commutes-with-Δ : ∀ (g h : G)
                           → (ℑ-unit ⁎ g) • (ℑ-unit ⁎ h) ⁻¹ ≈ ℑ-unit ⁎ (g • h ⁻¹)
    unit-commutes-with-Δ g h = 
                         (λ ξ → ℑ-unit ⁎ g • ξ) ⁎ application-commutes-with-inversion ℑ-unit h ⁻¹ 
                         • application-commutes-with-concatenation ℑ-unit g (h ⁻¹) ⁻¹

