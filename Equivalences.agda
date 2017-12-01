{-# OPTIONS --without-K #-}

module Equivalences where 

  open import Basics 
  open import EqualityAndPaths
  open import Language 
  open import Homotopies
  
  
  
  _left-inverse-of_ : ∀ {i j} {A : U i} {B : U j} → (f : A → B) → (g : B → A) → U j
  f left-inverse-of g =  (f ∘ g) ∼ id
  
  _right-inverse-of_ : ∀ {i j} {A : U i} {B : U j} → (f : A → B) → (g : B → A) → U i
  f right-inverse-of g = id ∼ (g ∘ f) 
  
  _is-quasiinverse-of_ : ∀ {i j} {A : U i} {B : U j} → (g : B → A) → (f : A → B) → U (i ⊔ j)
  g is-quasiinverse-of f = (g left-inverse-of f) × (g right-inverse-of f)   
  
  record _is-an-equivalence {i j} {A : U i} {B : U j} (f : A → B) : U (i ⊔ j) where
    constructor has-left-inverse_by_and-right-inverse_by_
    field
      left-inverse : B → A
      unit : left-inverse ∘ f ⇒ id
      right-inverse : B → A
      counit : id ⇒ f ∘ right-inverse 

  infixl 4 _≃_                                                -- \simeq
  record _≃_  {i j} (A : U i) (B : U j) : U (i ⊔ j) where
    constructor _is-an-equivalence-because_
    field 
      the-equivalence : A → B
      proof-of-invertibility : the-equivalence is-an-equivalence
  

  --inclusion
  map-as-equivalence : ∀ {A B : U₀} → (e : A → B) → e is-an-equivalence → A ≃ B
  map-as-equivalence e proof-of-equivalency = e is-an-equivalence-because proof-of-equivalency
  
  -- projections
  
  underlying-map-of : ∀ {i} {A B : U i} 
                      → A ≃ B → (A → B)
  underlying-map-of f = _≃_.the-equivalence f
  
  left-inverse-of-the-equivalence : 
    ∀ {i} {A B : U i} 
    → A ≃ B → (B → A)
  left-inverse-of-the-equivalence 
    (_ is-an-equivalence-because (has-left-inverse left-inverse by _ and-right-inverse _ by _)) = left-inverse
  
  right-inverse-of-the-equivalence : 
    ∀ {i} {A B : U i} 
    → A ≃ B → (B → A)
  right-inverse-of-the-equivalence 
    (_ is-an-equivalence-because (has-left-inverse _ by _ and-right-inverse right-inverse by _)) = right-inverse
  
  unit-of-the-equivalence : 
    ∀ {i} {A B : U i} 
    → (f : A ≃ B) → (left-inverse-of-the-equivalence f) ∘ (underlying-map-of f) ∼ id
  unit-of-the-equivalence 
    (_ is-an-equivalence-because (has-left-inverse _ by unit and-right-inverse _ by _)) = unit
  
  counit-of-the-equivalence : 
    ∀ {i} {A B : U i} 
    → (f : A ≃ B) → id ∼ (underlying-map-of f) ∘ (right-inverse-of-the-equivalence f) 
  counit-of-the-equivalence 
    (_ is-an-equivalence-because (has-left-inverse _ by _ and-right-inverse _ by counit)) = counit
  
  proof-of-equivalency :
    ∀ {A B : U₀} 
    → (f : A ≃ B) 
    → (underlying-map-of f) is-an-equivalence
  proof-of-equivalency (_ is-an-equivalence-because proof-of-equivalency) = 
    proof-of-equivalency
  
  inverse-of_given-by_ :
    ∀ {A B : U₀}
    → (f : A → B) → f is-an-equivalence
    → (B → A)
  inverse-of f given-by 
    (has-left-inverse left-inverse by _ and-right-inverse _ by _) = 
    left-inverse

  right-inverse-of_given-by_ :
    ∀ {A B : U₀}
    → (f : A → B) → f is-an-equivalence
    → (B → A)
  right-inverse-of f given-by 
    (has-left-inverse _ by _ and-right-inverse right-inverse by _) = 
    right-inverse

  counit-of_given-by_ :
    ∀ {A B : U₀}
    → (f : A → B) → (_ : f is-an-equivalence)
    → (id ⇒ _)
  counit-of f given-by 
    (has-left-inverse _ by _ and-right-inverse _ by counit) = 
     counit


  equivalence-proposition-as-sum-type :
    ∀ {A B : U₀} (f : A → B)
    → f is-an-equivalence ≃ ∑ (λ {(g , h) → (g ∘ f ⇒ id) × (id ⇒ f ∘ h)})
  equivalence-proposition-as-sum-type f =
    (λ {(has-left-inverse g by unit and-right-inverse h by counit) → ((g , h) , (unit , counit))})
      is-an-equivalence-because (has-left-inverse ((λ {((g , h) , (unit , counit)) →
                                   has-left-inverse g by unit and-right-inverse h by counit})) by (λ a → refl)
                                 and-right-inverse ((λ {((g , h) , (unit , counit)) →
                                   has-left-inverse g by unit and-right-inverse h by counit})) by (λ a → refl))


  type-of-equivalences-as-sum-type : 
    ∀ {A B : U₀}
    → (A ≃ B) ≃ ∑ (λ (f : A → B) → f is-an-equivalence)
  type-of-equivalences-as-sum-type =
      (λ {(f is-an-equivalence-because proof) → (f , proof)})
      is-an-equivalence-because
        (has-left-inverse (λ {(_ , _) → _}) by (λ _ → refl)
         and-right-inverse ((λ {(_ , _) → _})) by λ _ → refl)

  -- easy examples
  id-is-an-equivalence : ∀ {i} {A : U i} → id {i} {A} is-an-equivalence
  id-is-an-equivalence = has-left-inverse id by (λ x → refl) and-right-inverse id by (λ x → refl)

  transport-invertibility : ∀ {i j} {A : U i} (P : A → U j) {x y : A} 
                              → (γ : x ≈ y) → (p : P y) → transport P γ ( transport P (γ ⁻¹) p) ≈ p
  transport-invertibility P refl p = refl
  transport-invertibility-backwards : ∀ {i j} {A : U i} (P : A → U j) {x y : A} 
                              → (γ : x ≈ y) → (p : P x) → transport P (γ ⁻¹) ( transport P γ p) ≈ p
  transport-invertibility-backwards P refl p = refl
  
  transport-is-an-equivalence : ∀ {i j} {A : U i}  {x y : A} (P : A → U j)
                  → (γ : x ≈ y) → transport P γ is-an-equivalence
  transport-is-an-equivalence P γ = 
                              has-left-inverse transport P (γ ⁻¹) by 
                              transport-invertibility-backwards P γ 
                              and-right-inverse transport P (γ ⁻¹) by (λ p → (transport-invertibility P γ p) ⁻¹)
  
  transport-as-equivalence : ∀ {i j} {A : U i}  {x y : A} (P : A → U j) → (γ : x ≈ y) → P x ≃ P y
  transport-as-equivalence P γ = transport P γ is-an-equivalence-because
                                   transport-is-an-equivalence P γ
  
  
  equivalences-are-preserved-by-homotopy : 
    ∀ {A B : U₀} (f g : A → B)
    → f is-an-equivalence → f ∼ g
    → g is-an-equivalence
  equivalences-are-preserved-by-homotopy 
    f g (has-left-inverse left-inverse by unit and-right-inverse right-inverse by counit) H =
    has-left-inverse left-inverse by (λ a → left-inverse ⁎ H a ⁻¹ • unit a) 
    and-right-inverse right-inverse by (λ b → counit b • H (right-inverse b))

  the-map_is-an-equivalence-since-it-is-homotopic-to_by_which-is-an-equivalence-by_ :
    ∀ {A B : U₀} (f g : A → B)
    → f ∼ g → g is-an-equivalence
    → f is-an-equivalence
  the-map f is-an-equivalence-since-it-is-homotopic-to g by H which-is-an-equivalence-by g-is-an-equivalence =
    equivalences-are-preserved-by-homotopy g f g-is-an-equivalence (H ⁻¹∼)
  
  
  
  -- technical things for equivalences
  conjugate-by-counit : ∀ {A : U₀} {a a′ : A} (f : A → A)
                        → (H : id ∼ f) → (γ : a ≈ a′)
                        → H a ⁻¹ • γ • H a′ ≈ f ⁎ γ 
  conjugate-by-counit {_} {a} {a′} f H γ = ((cancel-the H a left-of f ⁎ γ) ⁻¹ •
                                                  •-is-associative (H a ⁻¹) (H a) (f ⁎ γ) ⁻¹
                                                  •
                                                  (concatenate H a ⁻¹ on-the-left-to
                                                   naturality-of-homotopies id f H γ)
                                                  • •-is-associative (H a ⁻¹) (id ⁎ γ) (H a′)
                                                  • (λ ζ → H a ⁻¹ • ζ • H a′) ⁎ id-has-trivial-application γ) ⁻¹
  
  
  conjugate-by-unit : ∀ {A : U₀} {a a′ : A} (f : A → A)
                        → (H : f ∼ id) → (γ : a ≈ a′)
                        → H a • γ • H a′ ⁻¹ ≈ f ⁎ γ 
  conjugate-by-unit {_} {a} {a′} f H γ = 
                        let compute-reverse : reverse-homotopy H a ⁻¹ ≈ H a
                            compute-reverse = ⁻¹-is-selfinverse (H a)
                        in (λ η → η • γ • reverse-homotopy H a′) ⁎ compute-reverse ⁻¹ •
                                conjugate-by-counit f (reverse-homotopy H) γ                                              
  
  
  -- obsoleted...
  uniqueness-of-left-inverses : ∀ {i} {A B : U i} (f : A → B) (g : B → A) (h : B → A)
                           → f is-an-equivalence → g ∘ f ∼ id → h ∘ f ∼ id → g ∼ h
  uniqueness-of-left-inverses f g h (has-left-inverse lf by unit and-right-inverse rf by counit) gf∼id hf∼id 
                        = λ b → (g ⁎ (counit b)) • (((λ a → gf∼id a • (hf∼id a)⁻¹) (rf b)) • (h ⁎ (counit b) ⁻¹)) 
  
  -- by the following three:
  left-and-right-inverse-are-homotopic : 
    ∀ {i} {A B : U i} (f : A → B) (l : B → A) (r : B → A)
    → l ∘ f ∼ id → id ∼ f ∘ r  
    → l ∼ r
  left-and-right-inverse-are-homotopic f l r unit counit b =
    let b≈frb : b ≈ (f ∘ r) b
        b≈frb = counit b
        lfrb≈rb : (l ∘ f) (r b) ≈ r b
        lfrb≈rb = unit (r b)
    in l ⁎ b≈frb • lfrb≈rb
  
  left-inverses-are-also-right-inverses : 
    ∀ {i} {A B : U i} (f : A → B) (l : B → A) (r : B → A)
    → l ∘ f ∼ id → id ∼ f ∘ r  
    → f ∘ l ∼ id
  left-inverses-are-also-right-inverses f l r unit counit b = 
    f ⁎ left-and-right-inverse-are-homotopic f l r unit counit b •
      counit b ⁻¹

  the-inverse-is-a-right-inverse-of_by_ :
    ∀ {A B : U₀} (f : A → B)
    → (proof : f is-an-equivalence)
    → id ⇒ f ∘ (inverse-of f given-by proof)
  the-inverse-is-a-right-inverse-of_by_ f
    (has-left-inverse l by unit and-right-inverse r by counit) =
      left-inverses-are-also-right-inverses f l r unit counit ⁻¹⇒

  right-inverses-are-also-left-inverses : 
    ∀ {i} {A B : U i} (f : A → B) (l : B → A) (r : B → A)
    → l ∘ f ∼ id → id ∼ f ∘ r  
    → id ∼ r ∘ f
  right-inverses-are-also-left-inverses f l r unit counit a = 
    unit a ⁻¹ •
      left-and-right-inverse-are-homotopic f l r unit counit (f a)
  
  
  id-as-equivalence : ∀ {i} {A : U i} → A ≃ A
  id-as-equivalence = id is-an-equivalence-because id-is-an-equivalence
  
  -- just language
  equivalent-by-definition = id-as-equivalence
  

  U-transport : ∀ {i} {A B : U i} → A ≈ B → A ≃ B
  U-transport refl = id-as-equivalence
  
  -- composition of equivalences 
  infixr 70 _∘≃_
  _∘≃_ : ∀ {i} {A B C : U i} (g : B ≃ C) (f : A ≃ B) → A ≃ C
  _∘≃_ {i} {A} {B} {C} (g is-an-equivalence-because (
                          has-left-inverse 
                            left-inverse-of-g by unit-for-g 
                          and-right-inverse 
                            right-inverse-of-g by counit-for-g))
   (f is-an-equivalence-because (has-left-inverse left-inverse-of-f by unit-for-f and-right-inverse right-inverse-of-f by counit-for-f)) = g ∘ f is-an-equivalence-because 
     (has-left-inverse left-inverse-of-f ∘ left-inverse-of-g by (_right-whisker_ {i} {A} {B} {A} {left-inverse-of-g ∘ (g ∘ f)} {f} 
                        (_left-whisker_ {i} {_} {_} {A} {B} {B} {left-inverse-of-g ∘ g} {id} 
                                    f  
                                    unit-for-g)  
                        left-inverse-of-f) •∼ 
                      unit-for-f and-right-inverse right-inverse-of-f ∘ right-inverse-of-g by
                        (counit-for-g •∼ (_right-whisker_ {i} {C} {B} {C} {right-inverse-of-g} {f ∘ (right-inverse-of-f ∘ right-inverse-of-g)} 
                          (_left-whisker_ {i} {_} {_} {C} {B} {B} {id} {f ∘ right-inverse-of-f} 
                          right-inverse-of-g 
                        counit-for-f))
                     g) )
  
  
  the-composition-of-equivalences-is-an-equivalence : 
    ∀ {A B C : U₀} (f : A → B) (g : B → C)
    → f is-an-equivalence → g is-an-equivalence
    → g ∘ f is-an-equivalence
  the-composition-of-equivalences-is-an-equivalence 
    f g proof-of-equivalency-of-f proof-of-equivalency-of-g =
    let f≃ = f is-an-equivalence-because proof-of-equivalency-of-f
        g≃ = g is-an-equivalence-because proof-of-equivalency-of-g
    in proof-of-equivalency (g≃ ∘≃ f≃)

  the-composition-of_and_is-an-equivalence,-since-the-first-one-is-by_and-the-second-by_ :
    ∀ {A B C : U₀} (f : A → B) (g : B → C)
    → f is-an-equivalence → g is-an-equivalence
    → g ∘ f is-an-equivalence
  the-composition-of f and g is-an-equivalence,-since-the-first-one-is-by f-is-an-equivalence and-the-second-by g-is-an-equivalence =
    the-composition-of-equivalences-is-an-equivalence f g f-is-an-equivalence g-is-an-equivalence
  
  -- application for equivalences
  infixl 60 _$≃_
  _$≃_ : ∀ {i} {A B : U i} → (f : A ≃ B) → A → B
  (f is-an-equivalence-because _) $≃ a = f a
  
  compute-$≃-on-transports : 
    ∀ {A : U₀} {x y z : A}
    → (γ : z ≈ y) 
    → (γ₀ : x ≈ z) → (transport-as-equivalence id ((λ ξ → x ≈ ξ) ⁎ γ)) $≃ γ₀ ≈ γ₀ • γ
  compute-$≃-on-transports refl refl = refl

  -- inversion of equivalences
  switch-inverses : ∀ {i} {A B : U i} {f : A → B} {g : B → A}
                → f is-an-equivalence → g ∘ f ∼ id → f ∘ g ∼ id --  g∼gfh ○ gfh∼h -> g∼h -> fg∼fh ○ fh∼1
  switch-inverses {_} {_} {_} {f} {g} (has-left-inverse k by H-kf-1 and-right-inverse h by H-fh-1) H-gf-1
                           = (((H-fh-1 right-whisker g) •∼ (h left-whisker H-gf-1)) right-whisker f) •∼ (H-fh-1 ⁻¹∼)
  
  infix 80 _⁻¹≃
  _⁻¹≃ : ∀ {i} {A B : U i} → A ≃ B → B ≃ A
  (the-equivalence is-an-equivalence-because reason) ⁻¹≃ with reason
  ... | (has-left-inverse
          left-inverse by unit
         and-right-inverse
          right-inverse by counit) 
      = left-inverse is-an-equivalence-because 
                 (has-left-inverse
                   the-equivalence by switch-inverses reason unit
                     and-right-inverse
                     the-equivalence by reverse-homotopy unit) 


  the-inverse-of_which-is-an-equivalence-by_is-again-an-equivalence :
    ∀ {A B : U₀} (f : A → B)
    → (equivalency : f is-an-equivalence)
    → (left-inverse-of-the-equivalence (f is-an-equivalence-because equivalency)) is-an-equivalence
  the-inverse-of f which-is-an-equivalence-by equivalency is-again-an-equivalence = 
    proof-of-equivalency ((f is-an-equivalence-because equivalency) ⁻¹≃)

  
  -- cancelling rules
  cancel-left :
    ∀ {A B C : U₀} (u : A → B)
    → (f : B ≃ C)
    → underlying-map-of (f ⁻¹≃) ∘ (underlying-map-of f ∘ u) ∼ u
  cancel-left u (f is-an-equivalence-because (has-left-inverse f⁻¹ by unit and-right-inverse _ by _)) a =
    unit (u a)
  
  cancel-right :
    ∀ {A B C : U₀} (u : B → C)
    → (f : A ≃ B)
    → (u ∘ underlying-map-of f) ∘ underlying-map-of (f ⁻¹≃) ∼ u
  cancel-right u (f is-an-equivalence-because (has-left-inverse f⁻¹ by unit and-right-inverse f⁻¹′ by counit)) b =
    u ⁎ left-inverses-are-also-right-inverses f f⁻¹ f⁻¹′ unit counit b

  
  
  --     r∘l
  --  A ----> C
  --    ↘   ↗  
  --  l   B   r
  module 2-out-of-3 {A B C : U₀} (l : A → B) (r : B → C) where
    the-composition-is-an-equivalence :
      l is-an-equivalence → r is-an-equivalence
      → r ∘ l is-an-equivalence
    the-composition-is-an-equivalence 
      l-is-an-equivalence r-is-an-equivalence  =
      proof-of-equivalency
        ((r is-an-equivalence-because r-is-an-equivalence) ∘≃
         (l is-an-equivalence-because l-is-an-equivalence))
  
    the-left-map-is-an-equivalence :
      r ∘ l is-an-equivalence → r is-an-equivalence
      → l is-an-equivalence
    the-left-map-is-an-equivalence
      r∘l-is-an-equivalence r-is-an-equivalence =
        let
          r-as-equivalence = (r is-an-equivalence-because r-is-an-equivalence)
          r⁻¹ = left-inverse-of-the-equivalence r-as-equivalence
          r⁻¹∘r∘l-as-an-equivalence = r-as-equivalence ⁻¹≃ ∘≃ ((r ∘ l) is-an-equivalence-because r∘l-is-an-equivalence)
          r⁻¹∘r∘l∼l = cancel-left l r-as-equivalence
        in equivalences-are-preserved-by-homotopy (r⁻¹ ∘ r ∘ l) l
             (proof-of-equivalency r⁻¹∘r∘l-as-an-equivalence) r⁻¹∘r∘l∼l
  
    the-right-map-is-an-equivalence :
      r ∘ l is-an-equivalence → l is-an-equivalence
      → r is-an-equivalence
    the-right-map-is-an-equivalence
      r∘l-is-an-equivalence l-is-an-equivalence =
        let
          l-as-equivalence = (l is-an-equivalence-because l-is-an-equivalence)
          l⁻¹ = left-inverse-of-the-equivalence l-as-equivalence
          r∘l∘l⁻¹-as-an-equivalence = ((r ∘ l) is-an-equivalence-because r∘l-is-an-equivalence) ∘≃ l-as-equivalence ⁻¹≃ 
          r∘l∘l⁻¹∼l = cancel-right r l-as-equivalence
        in equivalences-are-preserved-by-homotopy ((r ∘ l) ∘ l⁻¹) r
             (proof-of-equivalency r∘l∘l⁻¹-as-an-equivalence) r∘l∘l⁻¹∼l
  


  {-

    if e is an equivalence and we know fe ⇒ ge, then
    we also have f ⇒ g

  -}

  unwhisker-equivalence :
    ∀ {A B C : U₀} (f g : B → C) (e : A → B) 
    → e is-an-equivalence
    → f ∘ e ⇒ g ∘ e → f ⇒ g
  unwhisker-equivalence f g e e-is-an-equivalence H =
    let
      open _is-an-equivalence e-is-an-equivalence
      e⁻¹ = right-inverse
      cancel : id ⇒ e ∘ e⁻¹ 
      cancel = counit
    in λ b → f ⁎ counit b • (e⁻¹ left-whisker H) b • g ⁎ (counit b ⁻¹)


  -- reasoning
  infix 3 _≃∎
  infixr 2 _≃⟨_⟩_

  _≃∎ : ∀ {i} (A : U i) 
      → A ≃ A
  a ≃∎ = id-as-equivalence

  _≃⟨_⟩_ : ∀ {i} (A : U i) {B C : U i}
         → A ≃ B → B ≃ C → A ≃ C
  A ≃⟨ reason ⟩ e′ = e′ ∘≃ reason  
