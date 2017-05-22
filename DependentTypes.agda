{-# OPTIONS --without-K #-}

module DependentTypes where 
  open import Basics 
  open import EqualityAndPaths
  open import Homotopies
  open import Fiber
  open import Equivalences
  open import HalfAdjointEquivalences
  open import Pullback
  open import PullbackSquare
  -- univalence is needed to transform pullback-squares to
  -- morphisms over U₀
  open import Univalence

  
  record morphism-of-dependent-types (A′ A : U₀) (E′ : A′ → U₀) (E : A → U₀) : U₀ where
    constructor over_we-have-a-morphism-of-fibers_
    field 
      base-change : A′ → A
      morphism-of-fibers : (a′ : A′) → (E′(a′) → E(base-change a′))

  base-change-of :
    ∀ {A′ A : U₀} {E′ : A′ → U₀} {E : A → U₀}
    → (F : morphism-of-dependent-types A′ A E′ E)
    → (A′ → A)
  base-change-of (over base-change we-have-a-morphism-of-fibers _) = 
    base-change

  _on-the-fiber-over_ :
    ∀ {A′ A : U₀} {E′ : A′ → U₀} {E : A → U₀}
    → (F : morphism-of-dependent-types A′ A E′ E)
    → (a′ : A′)
    → (E′(a′) → E((base-change-of F) a′))
  (over _ we-have-a-morphism-of-fibers f) on-the-fiber-over a′ = f a′

  _is-an-equivalence-on-all-fibers : 
    ∀ {A′ A : U₀} {E′ : A′ → U₀} {E : A → U₀}
    → (F : morphism-of-dependent-types A′ A E′ E)
    → U₀
  (over f we-have-a-morphism-of-fibers e) is-an-equivalence-on-all-fibers = 
    ∀ (a′ : _) → e(a′) is-an-equivalence

  dependent-type_as-map :
    ∀ {A : U₀} 
    → (E : A → U₀)
    → (∑ E → A) 
  dependent-type E as-map = ∑π₁ 

  the-map-on-total-spaces-induced-by_ :
    ∀ {A′ A : U₀} {E′ : A′ → U₀} {E : A → U₀}
    → (F : morphism-of-dependent-types A′ A E′ E)
    → (∑ E′ → ∑ E)
  the-map-on-total-spaces-induced-by (over φ we-have-a-morphism-of-fibers f) = 
    λ {(a′ , e′) → ( φ(a′), (f a′)(e′) ) }

  dependent-replacement :
    ∀ {A B : U₀} (f : A → B)
    → (B → U₀)
  dependent-replacement f b = fiber-of f at b 

  fiber-transport-is-concatenation :
    ∀ {A B : U₀} (f : A → B)
    → (b b′ : B) → (γ : b ≈ b′)  
    → (a : A) (η : f(a) ≈ b) → transport (fiber-of f) γ (a is-in-the-fiber-by η) ≈ (a is-in-the-fiber-by η • γ)
  fiber-transport-is-concatenation f b .b refl a η = (λ ζ → a is-in-the-fiber-by ζ) ⁎ refl-is-right-neutral η


  -- the dependet replacement is equivalent as a map of types
  -- in the sense that the total spaces are equivalent
  -- and the triangle commutes (which is not shown because it does so definitionally)
  replacement-is-equivalent :
    ∀ {A B : U₀} (f : A → B)
    → ∑ (dependent-replacement f) ≃ A
  replacement-is-equivalent f = (λ {(b , (a is-in-the-fiber-by γ)) → a}) is-an-equivalence-because
    (has-left-inverse (λ a → f a , (a is-in-the-fiber-by refl))
      by (λ { (b , (a is-in-the-fiber-by γ))
                  →  f a , (a is-in-the-fiber-by refl)
                    ≈⟨ equality-action-on-∑ (f a) b γ (a is-in-the-fiber-by refl) ⟩
                     (b , transport (fiber-of f) γ (a is-in-the-fiber-by refl))
                    ≈⟨ (λ z → b , z) ⁎ fiber-transport-is-concatenation f (f a) b γ a refl ⟩ 
                      b , (a is-in-the-fiber-by γ) ≈∎
              })

     and-right-inverse (λ a → f a , (a is-in-the-fiber-by refl)) by (λ x → refl))

  ∑-over-One-is-trivial :
    ∀ (P : One → U₀)
    → ∑ P ≈ P(∗)
  ∑-over-One-is-trivial P = univalence
    ((λ {(∗ , p) → p }) is-an-equivalence-because
      (has-left-inverse (λ p → ∗ , p) by (λ {(∗ , p) → refl})
       and-right-inverse (λ p → ∗ , p) by (λ p → refl)))

  replacement-over-One-is-constant :
    ∀ {A : U₀} (f : A → One)
    → (dependent-replacement f) ∗ ≈ A
  replacement-over-One-is-constant f = ∑-over-One-is-trivial (dependent-replacement f) ⁻¹
                                       • univalence (replacement-is-equivalent f)

  pullback-of_along-dependent-tpye :
    ∀ {A : U₀} (P : A → U₀)
    → (E : A → U₀)
    → (∑ P → U₀)
  pullback-of P along-dependent-tpye E (a , pₐ) = E a

  -- ∑ formal-disk-at a = ∑ formal-disk-at (a , pₐ) = ∑ (ι(a′ , pₐ′) ≈ ι(a , pₐ))
  -- pullback = fibration of products bzw. 
  -- (type of pullbacks over base A) = (A -> type of products)

  module pullbacks-are-fiberwise-equivalences 
        {Z A B C : U₀}
        {f : A → C}  {g : B → C}
        {z₁ : Z → A} {z₂ : Z → B}
        (□ : pullback-square f g z₁ z₂) where
      
  {-

        Z -z₁→ A
        |      |
        z₂     f
        |      |
        v      v
        B -g-→ C

  -}

     left-fiber-square-at_ : (b : B) → _
     left-fiber-square-at b = fiber-square-for z₂ at b

     right-fiber-square-at_ : (b : B) → _
     right-fiber-square-at b = fiber-square-for f at (g b)

  {-
    paste in the following diagram to get an equivalence on the fibers

     Fz₂──→Z -z₁→ A←────Fg
     |⌟    |⌟     |     ⌞|
     |     z₂     f      |
     |     |      |      |
     ↓     ↓      ↓      ↓
     1 ─b─→B ─g─→ C←g(b)─1 

  -}
     second-right-square-at_ : (b : B) → _
     second-right-square-at b = pasting-of-pullback-squares (left-fiber-square-at b) □

     equivalence-at_ : (b : B) → fiber-of z₂ at b ≃ fiber-of f at (g b)
     equivalence-at b = deduce-equivalence-of-vertices (second-right-square-at b)
                          (right-fiber-square-at b)

     as-triangle-over-the-universe : dependent-replacement z₂ ⇒ dependent-replacement f ∘ g
     as-triangle-over-the-universe b = univalence (equivalence-at b)

  module fiberwise-equivalences-are-pullbacks {A′ A : U₀} {E′ : A′ → U₀} {E : A → U₀} 
      (F : morphism-of-dependent-types A′ A E′ E)
      (F-is-an-equivalence-on-fibers : F is-an-equivalence-on-all-fibers) where

      open _is-an-equivalence

      f = base-change-of F


      g : (a′ : A′) → (E′ a′ → E _)
      g a′ = F on-the-fiber-over a′
      g⁻¹ : (a′ : A′) → (E _ → E′ a′)
      g⁻¹ a′ = inverse-of (g a′) given-by (F-is-an-equivalence-on-fibers a′)

      left-invertible-at : (a′ : A′) → g⁻¹ a′ ∘ g a′ ⇒ id
      left-invertible-at a′ = unit (F-is-an-equivalence-on-fibers a′)
      right-invertible-at : (a′ : A′) → id ⇒ g a′ ∘ g⁻¹ a′
      right-invertible-at a′ =
        the-inverse-is-a-right-inverse-of g a′ by F-is-an-equivalence-on-fibers a′

      g-on-∑ : ∑ E′ → ∑ E
      g-on-∑ (a′ , e′) = (f a′ , g a′ e′)

      p′ : ∑ E′ → A′
      p′ = ∑π₁
      p : ∑ E → A
      p = ∑π₁

      f∘p′⇒p∘g-on-∑  : f ∘ p′ ⇒ p ∘ g-on-∑ 
      f∘p′⇒p∘g-on-∑ (a′ , e′) = refl

      induced-map′ : ∑ E′ → pullback p f
      induced-map′ (a′ , e′) = (f a′ , (g a′) e′) and a′ are-in-the-same-fiber-by refl

      induced-map : ∑ E′ → pullback p f
      induced-map = induced-map-to-pullback g-on-∑ ∑π₁ f∘p′⇒p∘g-on-∑

      induced-map⇒induced-map′ : induced-map ⇒ induced-map′
      induced-map⇒induced-map′ (a′ , e′) = refl
      
      induced-map⁻¹ : pullback p f → ∑ E′
      induced-map⁻¹ ((a , e) and a′ are-in-the-same-fiber-by γ) = 
        (a′ , g⁻¹ a′ (transport E γ e))

      left-invertible : induced-map⁻¹ ∘ induced-map  ⇒ id 
      left-invertible (a′ , e′) =   induced-map⁻¹ (induced-map (a′ , e′))
                                 ≈⟨ induced-map⁻¹ ⁎ induced-map⇒induced-map′ (a′ , e′) ⟩
                                    induced-map⁻¹ (induced-map′ (a′ , e′))
                                 ≈⟨ refl ⟩
                                   (a′ , g⁻¹ a′ (transport E refl (g a′ e′)))
                                 ≈⟨ refl ⟩ 
                                   (a′ , g⁻¹ a′ (id (g a′ e′)))
                                 ≈⟨ (λ (e : E′ a′) → a′ , e) ⁎ left-invertible-at a′ e′ ⟩ 
                                   (a′ , e′)
                                 ≈∎

      abstract
        right-invertible : id ⇒ induced-map ∘ induced-map⁻¹
        right-invertible ((a , e) and a′ are-in-the-same-fiber-by γ) =
                    let calculate-some-equality :  (a , e) ≈ (f a′ , g a′ (g⁻¹ a′ (transport E γ e)))
                        calculate-some-equality = (a , e)
                                                 ≈⟨ equality-action-on-∑ a (f a′) γ e ⟩
                                                  (f a′ , transport E γ e)
                                                 ≈⟨ (λ e′ → f a′ , e′) ⁎ right-invertible-at a′ (transport E γ e) ⟩
                                                  (f a′ , g a′ (g⁻¹ a′ (transport E γ e)))
                                                 ≈∎
                        calculate-p⁎-of-this-equality : p ⁎ calculate-some-equality ≈ γ
                        calculate-p⁎-of-this-equality =
                           p ⁎ ((equality-action-on-∑ a (f a′) γ e) • (((λ e′ → f a′ , e′) ⁎ right-invertible-at a′ (transport E γ e)) • refl))
                          ≈⟨ application-commutes-with-concatenation p (equality-action-on-∑ a (f a′) γ e) _ ⟩
                           p ⁎ (equality-action-on-∑ a (f a′) γ e) • p ⁎ (((λ e′ → f a′ , e′) ⁎ right-invertible-at a′ (transport E γ e)) • refl)
                          ≈⟨ (λ η → η • p ⁎ (((λ e′ → f a′ , e′) ⁎ right-invertible-at a′ (transport E γ e)) • refl)) ⁎ cancel-equality-action-on-∑-with-projection a (f a′) γ e ⟩ 
                           γ • p ⁎ (((λ e′ → f a′ , e′) ⁎ right-invertible-at a′ (transport E γ e)) • refl)
                          ≈⟨ (λ η → γ • η) ⁎
                               (λ ζ → p ⁎ ζ) ⁎
                                refl-is-right-neutral ((λ e′ → f a′ , e′) ⁎ right-invertible-at a′ (transport E γ e)) ⁻¹ ⟩ 
                           γ • p ⁎ ((λ e′ → f a′ , e′) ⁎ right-invertible-at a′ (transport E γ e))
                          ≈⟨ (λ η → γ • η) ⁎
                               cancel-orthogonal-equality-in-∑ (f a′) _ _ (right-invertible-at a′ (transport E γ e)) ⟩ 
                           γ • refl
                          ≈⟨ refl-is-right-neutral γ ⁻¹ ⟩ 
                           γ
                          ≈∎




                    in ((a , e) and a′ are-in-the-same-fiber-by γ)
                      ≈⟨ (λ η → (a , e) and a′ are-in-the-same-fiber-by η) ⁎
                            (γ
                           ≈⟨ calculate-p⁎-of-this-equality ⁻¹ ⟩
                            p ⁎ calculate-some-equality
                           ≈⟨ ⁻¹-is-selfinverse (p ⁎ calculate-some-equality) ⁻¹ ⟩
                            (p ⁎ calculate-some-equality ⁻¹) ⁻¹
                           ≈⟨ (λ η → η ⁻¹) ⁎ application-commutes-with-inversion p calculate-some-equality ⁻¹ ⟩
                            p ⁎ (calculate-some-equality ⁻¹) ⁻¹
                           ≈⟨ refl-is-right-neutral _ ⟩
                            p ⁎ (calculate-some-equality ⁻¹) ⁻¹ • refl ≈∎) ⟩ 
                       (a , e) and a′ are-in-the-same-fiber-by p ⁎ (calculate-some-equality ⁻¹) ⁻¹ • refl
                      ≈⟨ equality-action p f (f a′ , g a′ (g⁻¹ a′ (transport E γ e)))
                           (a , e) (calculate-some-equality ⁻¹) a′ refl ⁻¹ ⟩ 
                       (f a′ , (g a′) (g⁻¹ a′ (transport E γ e))) and a′ are-in-the-same-fiber-by refl
                      ≈⟨ refl ⟩
                       induced-map′ (a′ , g⁻¹ a′ (transport E γ e))
                      ≈⟨ induced-map⇒induced-map′ _ ⟩
                       induced-map (a′ , g⁻¹ a′ (transport E γ e))
                      ≈∎
      
      

      fiberwise-equivalences-are-pullbacks :
        pullback-square-with-right (dependent-type E as-map)
         bottom base-change-of F
         top the-map-on-total-spaces-induced-by F
         left (dependent-type E′ as-map)
      fiberwise-equivalences-are-pullbacks = 
        the-square-commuting-by f∘p′⇒p∘g-on-∑ 
        and-inducing-an-equivalence-by
          (has-left-inverse induced-map⁻¹ by left-invertible
           and-right-inverse induced-map⁻¹ by right-invertible)


  fibered-morphisms-are-slice-homs :
    ∀ {S T X : U₀} (φₛ : S → X) (φₜ : T → X)
    → ∑ (λ ψ → φₜ ∘ ψ ⇒ φₛ) ≃ Π (λ (s : S) → fiber-of φₜ at (φₛ s))
  fibered-morphisms-are-slice-homs φₛ φₜ =
    let
      inverse = (λ ψₛ → ((λ s → ι-fiber (ψₛ s)) , (λ s → fiber-of.γ (ψₛ s))))
    in (λ {(ψ , H) s → (ψ s) is-in-the-fiber-by H s}) is-an-equivalence-because
     (has-left-inverse inverse
        by (λ {(ψ , H) → refl})
      and-right-inverse inverse
        by (λ ψₛ → refl))

  if-fibered-morphisms-are-equal-the-underlying-maps-are-homotopic :
    ∀ {S T X : U₀} (φₛ : S → X) (φₜ : T → X)
    → (ψ ψ′ : Π (λ (s : S) → fiber-of φₜ at (φₛ s)))
    → ψ ≈ ψ′ → (λ s → ι-fiber (ψ s)) ⇒ (λ s → ι-fiber (ψ′ s))
  if-fibered-morphisms-are-equal-the-underlying-maps-are-homotopic φₛ φₜ ψ ψ′ γ =
    λ s → ι-fiber ⁎ (λ f → f s) ⁎ γ
  
  -- this would should better be in some pullback-module,
  -- but due to some dependecy issues, it is here...
  module pullback-preserves-equivalences
    {A B C : U₀} (f : A → B) (g : C → B) (f-is-an-equivalence : f is-an-equivalence) where

  {-
    we pullback f and want to show that f′ is also an equivalence
   _  ───→ A
   | ⌟     |
   f′      f
   ↓       ↓
   C ──g─→ B
  -}

    □-with-f : pullback-square-with-right f
                 bottom g
                 top _
                 left _
    □-with-f = complete-to-pullback-square f g

    f′ : _ → C
    f′ = left-map-of □-with-f

  {-

    fiber-of f′ at c ─ι→_
                | ⌟     |
                |       f′
                ↓       ↓
                1 ────→ C
  -}

    fiber-□-for-f′ :
      ∀ (c : C)
      → pullback-square-with-right f′
           bottom (λ _ → c)
           top ι-fiber
           left (λ _ → ∗)
    fiber-□-for-f′ c = fiber-square-for f′ at c



  {-
    get the following by pasting:

   fiber-of f′ at c ──→ A
                | ⌟     |
                |       f
                ↓       ↓
                1 ────→ B
  -}

    pasted-□ :
      ∀ (c : C)
      → pullback-square-with-right f
           bottom (g ∘ (λ _ → c))
           top _
           left _
    pasted-□ c = pasting-of-pullback-squares
                   (fiber-□-for-f′ c)
                   □-with-f     

  {-
    compare this square with a corresponding fiber square of f
  -}

    the-fiber-is-equivalent-to-a-fiber-of-f :
      ∀ (c : C)
      → fiber-of f′ at c ≃ fiber-of f at (g c)
    the-fiber-is-equivalent-to-a-fiber-of-f c =
      deduce-equivalence-of-vertices
        (pasted-□ c) (fiber-square-for f at g c)

    {-
      conclude that all fibers are contractible
    -}

    open import EquivalenceCharacterization
    open import Contractibility
    
    all-fibers-are-contractible :
      ∀ (c : C)
      → (fiber-of f′ at c) is-contractible
    all-fibers-are-contractible c =
      types-equivalent-to-contractibles-are-contractible
        (the-fiber-is-equivalent-to-a-fiber-of-f c)
        (contractible-fibers-characterize-equivalences.to-fiber-condition
          f f-is-an-equivalence (g c))

    conclusion :
      f′ is-an-equivalence
    conclusion =
      contractible-fibers-characterize-equivalences.from-fiber-condition
        f′ all-fibers-are-contractible


    -- this is a better version of the
    -- deduce-equivalence... function in PullbackSquare
    -- since it preserves the 2-cell
    reverse-statement :
      ∀ {Z : U₀}
      → (z₁ : Z → A) (z₂ : Z → C)
      → (γ : f ∘ z₁ ⇒ g ∘ z₂)
      → z₂ is-an-equivalence
      → pullback-square-with-right f
          bottom g
          top z₁
          left z₂
    reverse-statement {Z} z₁ z₂ γ z₂-is-an-equivalence =
      let
        ψ : Z → pullback f g
        ψ = induced-map-to-pullback z₁ z₂ γ
        ψ-is-an-equivalence : ψ is-an-equivalence
        ψ-is-an-equivalence = 2-out-of-3.the-left-map-is-an-equivalence ψ f′ z₂-is-an-equivalence conclusion 
      in the-square-commuting-by γ and-inducing-an-equivalence-by ψ-is-an-equivalence
      

  {-
    ∑ P - - ∑ Q
     |       |
     ↓       ↓ 
     A ─f──→ B  

    if f is an equivalence and the fiber over a and f(a) are equivalent,
    there is an equivalence on the total spaces.
    (This turned out to be proven also in HoTT-Book, Thm 4.7.7)
  -}
  module fiber-equivalences-along-an-equivalence-on-the-base
    {A B : U₀} (P : A → U₀) (Q : B → U₀)
    (f≃ : A ≃ B) (s≃ : (a : A) → P a ≃ Q ((underlying-map-of f≃) a)) where

    -- some shortahnds
    f = underlying-map-of f≃

    s : (a : A) → P a → Q (f a)
    s a = underlying-map-of (s≃ a)

    f-as-morphism-of-dependent-types : morphism-of-dependent-types A B P Q
    f-as-morphism-of-dependent-types = record{ base-change = f; morphism-of-fibers = s}

    induced-map : ∑ P → ∑ Q
    induced-map = the-map-on-total-spaces-induced-by f-as-morphism-of-dependent-types

    -- s ⇒ induced-map?

    □₁ : pullback-square-with-right ∑π₁
           bottom f
           top induced-map
           left ∑π₁
    □₁ = fiberwise-equivalences-are-pullbacks.fiberwise-equivalences-are-pullbacks
           f-as-morphism-of-dependent-types
           (λ a → proof-of-equivalency (s≃ a))


    pullback-of-f-along-π₁ : _ → ∑ Q
    pullback-of-f-along-π₁ = pullback-preserves-equivalences.f′ f ∑π₁ (proof-of-equivalency f≃)

    -- use that pullbacks of equivalences are equivalences


    □₂ : pullback-square-with-right (∑π₁-from Q)
           bottom f
           top _
           left _
    □₂ = rotate-cospan (pullback-preserves-equivalences.□-with-f f ∑π₁ (proof-of-equivalency f≃))
    
  {-
    in this last step, we use both pullback squares
    to see that the induced map (∑ P ---→ ∑ Q) is an 
    equivalence.
    This follows since f′ is one as the pullback of an 
    equivalence and the induced map Z → ∑ P is an 
    equivalence, both pullbacks are pullbacks of the same 
    cospan.

    Z────────f′
    | ↘        ↘
    | ∑ P --→ ∑ Q
    |  |       |
    \  ↓       ↓ 
     ↘ A ─f──→ B  

  -}

    induced-map-is-an-equivalence :
      induced-map is-an-equivalence
    induced-map-is-an-equivalence =
      let
        Z = upper-left-vertex-of □₂
        f′ : Z → ∑ Q
        f′ = pullback-preserves-equivalences.f′ f (∑π₁-from Q) (proof-of-equivalency f≃)
        f′≃ : Z ≃ ∑ Q  
        f′≃ = f′ is-an-equivalence-because
          (pullback-preserves-equivalences.conclusion f ∑π₁ (proof-of-equivalency f≃))
        φ≃ : ∑ P ≃ Z
        φ≃ = deduce-equivalence-of-vertices □₁ □₂
        φ : ∑ P → Z
        φ = underlying-map-of φ≃
      in the-map induced-map is-an-equivalence-since-it-is-homotopic-to f′ ∘ φ by
         (λ _ → refl) which-is-an-equivalence-by proof-of-equivalency (f′≃ ∘≃ φ≃)

