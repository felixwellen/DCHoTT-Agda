{-# OPTIONS --without-K #-}

module FormalDisk where
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Language
  open import Equivalences
  open import CommonEquivalences
  open import Im
  open import DependentTypes
  open import Fiber
  open import Contractibility
  open import HomogeneousType


  _is-infinitesimally-close-to_ :
    {X : 𝒰₀} → (x x′ : X) → 𝒰₀
  x is-infinitesimally-close-to x′ = ℑ-unit x ≈ ℑ-unit x′

  private
    -- shorthand
    _~_ :
      {X : 𝒰₀} → (x x′ : X) → 𝒰₀
    _~_ = _is-infinitesimally-close-to_

  -- shorthand
  _is-close-to_ :
    {X : 𝒰₀} → (x x′ : X) → 𝒰₀
  _is-close-to_ = _is-infinitesimally-close-to_


  -- since all maps preserve smooth structure,
  -- they also preserve infinitesimal proximity:

  mapping-with_preserves-infinitesimal-proximity :
    ∀ {X Y : 𝒰₀} {x x′ : X}
    → (f : X → Y)
    → (x ~ x′) → (f x) ~ (f x′)
  mapping-with f preserves-infinitesimal-proximity γ = ℑ⁎ f ⁎ γ  -- see 'Im.agda'


  -- T∞ as dependent type
  formal-disk-at_ :
    ∀ {X : 𝒰₀}
    → (x : X) → 𝒰₀
  formal-disk-at x = ∑ (λ x′ → x ~ x′)

  𝔻 :
    ∀ (X : 𝒰₀)
    → (x : X) → 𝒰₀
  𝔻 X x = formal-disk-at x

  𝔻ᵣ :
    ∀ (X : 𝒰₀)
    → (x : ℑ X) → 𝒰₀
  𝔻ᵣ X x = ∑ (λ x′ → x ≈ ℑ-unit x′)

  inclusion-of-formal-disk-at :
    ∀ {X : 𝒰₀}
    → (x : X)
    → formal-disk-at x → X
  inclusion-of-formal-disk-at x (y , γ) = y

  ι-𝔻 = inclusion-of-formal-disk-at

  ∗-𝔻 :
    ∀ {X : 𝒰₀} {x : X}
    → 𝔻 X x
  ∗-𝔻 = (_ , refl)


  induced-map-on-formal-disks :
    ∀ {X Y : 𝒰₀}
    → (f : X → Y)
    → (x : X) → 𝔻 _ x → 𝔻 _ (f x)
  induced-map-on-formal-disks f x (x′ , x′-is-close-to-x) =
    (f x′ , (ℑ⁎ f ⁎ x′-is-close-to-x))

  -- first order terminology
  push-forward :
    ∀ {X Y : 𝒰₀}
    → (f : X → Y)
    → (x : X) → 𝔻 _ x → 𝔻 _ (f x)
  push-forward = induced-map-on-formal-disks

  -- the generalized differential of a function
  d :
    ∀ {X Y : 𝒰₀}
    → (f : X → Y)
    → (x : X) → 𝔻 _ x → 𝔻 _ (f x)
  d f x (x′ , x′~x) = induced-map-on-formal-disks f x (x′ , x′~x)

  chain-rule :
    ∀ {X Y Z : 𝒰₀}
    → (f : X → Y) → (g : Y → Z)
    → (x : X) → (x+ε : 𝔻 X x)
    → d (g ∘ f) x x+ε ≈ (d g (f x) ∘ d f x) x+ε
  chain-rule f g x 𝒹@(x+ε , x~x+ε) =
    d (g ∘ f) x 𝒹         ≈⟨ step1 ⟩
    (d g (f x) ∘ d f x) 𝒹 ≈∎
    where
      y = g (f x+ε)
      step1 : _ ≈ _
      step1 = (λ y+δ → (g (f x+ε) , y+δ))
        ⁎ ((ℑ⁎ g ∘ f ⁎ x~x+ε)       ≈⟨ ℑ⁎-commutes-with-∘ f g x~x+ε ⟩
            (ℑ⁎ g ⁎ (ℑ⁎ f ⁎ x~x+ε)) ≈∎)


  module equivalences-induce-equivalences-on-formal-disks
    {A B : 𝒰₀} (f≃ : A ≃ B) where

    f = underlying-map-of f≃

    ℑf⁎-is-an-equivalence : (x y : A) → (λ (γ : x is-close-to y) → ℑ⁎ f ⁎ γ) is-an-equivalence
    ℑf⁎-is-an-equivalence =
      equivalences-induce-equivalences-on-the-coreduced-identity-types.ℑf⁎-is-an-equivalence f≃

    df-is-an-equivalence : (a : A) → (d f a) is-an-equivalence
    df-is-an-equivalence a =
      fiber-equivalences-along-an-equivalence-on-the-base.induced-map-is-an-equivalence
        (λ x → a is-close-to x) (λ y → f a is-close-to y) f≃
        (λ x →
           (λ (γ : a is-close-to x) → ℑ⁎ f ⁎ γ) is-an-equivalence-because
           ℑf⁎-is-an-equivalence a x)

    conclusion : (a : A) → formal-disk-at a ≃ formal-disk-at (f a)
    conclusion a = (d f a) is-an-equivalence-because (df-is-an-equivalence a)


  {-
    this is essentially the fact that
    derivatives of functions into products
    may be calculated componentwise
  -}

  module 𝔻-commutes-with-× {A B C : 𝒰₀} (f : A → B × C) where
    open ℑ-preserves-products B C

    df : (x : A) → 𝔻 A x → 𝔻 (B × C) (f x)
    df = d f

    df₁ : (x : A) → 𝔻 A x → 𝔻 B (π₁ (f x))
    df₁ = d (π₁ ∘ f)

    df₂ : (x : A) → 𝔻 A x → 𝔻 C (π₂ (f x))
    df₂ = d (π₂ ∘ f)

    split-𝔻× : (y : B × C)
      → 𝔻 (B × C) y → 𝔻 B (π₁ y) × 𝔻 C (π₂ y)
    split-𝔻× (b₀ , c₀) ((b , c) , γ) =
      let
        b₀-close-to-b : b₀ is-close-to b
        b₀-close-to-b =
               ι b₀
              ≈⟨ φ⁻¹-commutes-with-π₁ (b₀ , c₀) ⁻¹ ⟩
               π₁ (φ⁻¹ (ι (b₀ , c₀)))
              ≈⟨ π₁ ⁎ φ⁻¹ ⁎ γ ⟩
               π₁ (φ⁻¹ (ι (b , c)))
              ≈⟨ φ⁻¹-commutes-with-π₁ (b , c)  ⟩
               ι b
              ≈∎

        c₀-close-to-c : c₀ is-close-to c
        c₀-close-to-c =
               ι c₀
              ≈⟨ φ⁻¹-commutes-with-π₂ (b₀ , c₀) ⁻¹ ⟩
               π₂ (φ⁻¹ (ι (b₀ , c₀)))
              ≈⟨ π₂ ⁎ φ⁻¹ ⁎ γ ⟩
               π₂ (φ⁻¹ (ι (b , c)))
              ≈⟨ φ⁻¹-commutes-with-π₂ (b , c)  ⟩
               ι c
              ≈∎
      in
         ((b , b₀-close-to-b)
        , (c , c₀-close-to-c))

    join-𝔻× : (y : B × C)
      → 𝔻 B (π₁ y) × 𝔻 C (π₂ y) → 𝔻 (B × C) y
    join-𝔻× (b₀ , c₀) ((b , b₀∼b) , (c , c₀∼c)) =
      ((b , c) , pair-construction b₀ c₀ ⁻¹ • φ ⁎ (b₀∼b ,≈ c₀∼c) • pair-construction b c)


    {- ... -}


  formal-disk-of :
    ∀ {V : 𝒰₀}
    → (structure-on-V : homogeneous-structure-on V)
    → 𝒰₀
  formal-disk-of structure-on-V =
    formal-disk-at (homogeneous-structure-on_.e structure-on-V)
