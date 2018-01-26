{-# OPTIONS --without-K #-}

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
  open import EtaleMaps hiding (underlying-map-of)
  open import DependentTypes
  open import Fiber
  open import Contractibility
  open import HomogeneousType
  open import FormalDisk
  
  -- formal disk at a point as pullback
  --  
  -- D ---> ∗
  -- | ⌟    |
  -- |      x₀
  -- ↓      ↓
  -- X ---> ℑ X
  D : ∀ (X : U₀) → (x₀ : X) → U₀
  D X x₀ = pullback (λ (x : One) → ℑ-unit x₀) (ℑ-unit-at X)

  {-
    the jet bundle
  -}
  J∞ :
    ∀ {X : U₀}
    → (E : X → U₀)
    → (X → U₀)
  J∞ E x = formal-disk-at x → E(x)

  J∞→ :
    ∀ {X : U₀}
    → {E : X → U₀} {F : X → U₀}
    → (φ : (x : X) → E x → F x)
    → ((x : X) → J∞ E x → J∞ F x)
  J∞→ {_} {E} {_} φ x = λ (f : formal-disk-at x → E x) → φ x ∘ f

  {-

    a section of the bundle is mapped to
    the dependent function of its jets

  -}

  j∞ : ∀ {X : U₀}
    → (E : X → U₀)
    → Π E → Π (J∞ E)
  j∞ {X} E s = λ (x : X) (γ : formal-disk-at x) → s x

  {-
    the relative formal disk bundle
  -}

  T∞′ : 
    ∀ {X : U₀}
    → (E : X → U₀)
    → (X → U₀)
  T∞′ E x = (formal-disk-at x) × E(x)

{-
  T∞′-of-the-inclusion-of_is-the-formal-disk :
    ∀ {X : U₀}
    → (x₀ : X)
    → (T∞′ (dependent-replacement (λ ∗ → x₀))) ≃χ (λ (x : X) → x is-infinitesimally-close-to x₀)
  T∞′-of-the-inclusion-of x₀ is-the-formal-disk =
    let
      map-to = {!!}
    in over id-as-equivalence
      there-is-the-equivalence (λ x → {!!})
  -}
  {-
    T is fiberwise left adjoint to J:
      ∀ (x : X) E(x) → J∞(F)(x) ≃ T∞(E)(x) → F(x)
  -}

  fiberwise-adjunction-of-T∞-and-J∞ :
    ∀ {X : U₀}
    → (E : X → U₀) (F : X → U₀)
    → (x : X) → (E(x) → J∞(F)(x)) ≃ (T∞′(E)(x) → F(x))
  fiberwise-adjunction-of-T∞-and-J∞ E F x =
    let
      map-to : (E(x) → J∞(F)(x)) → (T∞′(E)(x) → F(x))
      map-to f = λ {(dx , eₓ) → f eₓ dx}
      map-from : (T∞′(E)(x) → F(x)) → (E(x) → J∞(F)(x))
      map-from f = λ eₓ dx → f (dx , eₓ)
    in map-to is-an-equivalence-because
       (has-left-inverse map-from by (λ _ → refl)
        and-right-inverse map-from by (λ _ → refl))



  -- the definitions of the formal disk agree
  module pullback-and-sum-definition-of-formal-disks-are-equivalent
    {X : U₀} (x₀ : X) where

    D-pullback = D X x₀
    D-sum = formal-disk-at x₀
{-
    conclusion : D-pullback ≃ D-sum
    conclusion = (λ {(∗ and x are-in-the-same-fiber-by γ) → (x , γ ⁻¹)})
      is-an-equivalence-because
        (has-left-inverse (λ {(x , γ) → (∗ and x are-in-the-same-fiber-by γ ⁻¹)})
           by (λ {(∗ and x are-in-the-same-fiber-by γ) → ⁻¹-is-selfinverse γ ⁻¹})
         and-right-inverse (λ {(x , γ) → (∗ and x are-in-the-same-fiber-by γ ⁻¹)})
           by (λ {(x , γ) → refl}))
-}
  T∞→ = induced-map-on-formal-disks

  formal-disk-bundle : (X : U₀) → U₀
  formal-disk-bundle X = pullback (ℑ-unit-at X) (ℑ-unit-at X)

  T∞ : (X : U₀) → U₀
  T∞ X = formal-disk-bundle X

  T∞-as-dependent-type :
    (X : U₀) → X → U₀
  T∞-as-dependent-type X x = formal-disk-at x 
  
  p-of-T∞ : (X : U₀) → (T∞ X) → X
  p-of-T∞ X = p₁-of-pullback (ℑ-unit-at X) (ℑ-unit-at X)

  formal-disk-bundle-as-pullback-square :
    ∀ (X : U₀) → pullback-square-with-right ℑ-unit bottom ℑ-unit top p₁ left p₂
  formal-disk-bundle-as-pullback-square X = complete-to-pullback-square (ℑ-unit-at X) (ℑ-unit-at X)

  {-
    we have two versions of the disk bundle, 
    one constructed as a pullback, the other
    as the sum over the T∞-as-dependent-type
  -}
  module pullback-definition-and-dependent-version-agree (X : U₀) where

    φ : T∞ X → ∑ (T∞-as-dependent-type X)
    φ (x and y are-in-the-same-fiber-by γ) = (x , (y , γ))

    φ⁻¹ : ∑ (T∞-as-dependent-type X) → T∞ X
    φ⁻¹ (x , (y , γ)) = x and y are-in-the-same-fiber-by γ

    conclusion : T∞ X ≃ ∑ (T∞-as-dependent-type X)
    conclusion = φ is-an-equivalence-because
      (has-left-inverse φ⁻¹ by (λ _ → refl)
       and-right-inverse φ⁻¹ by (λ _ → refl))

    on-fibers′ : (x : X) → fiber-of (∑π₁-from (T∞-as-dependent-type X)) at x ≃ formal-disk-at x
    on-fibers′ x = fiber-of-a-∑ x

    on-fibers : (x : X) → fiber-of (p-of-T∞ X) at x ≃ formal-disk-at x
    on-fibers x =
        on-fibers′ x
      ∘≃ (
        pullbacks-are-fiberwise-equivalences.equivalence-at_
          (pullback-square-from-equivalence-of-maps
            (∑π₁-from T∞-as-dependent-type X) (p-of-T∞ X) conclusion id-as-equivalence (λ _ → refl)) x)

  module paths-induce-equivalences-of-formal-disks
    {A : U₀} {x y : A} (γ : x ≈ y) where

    transport-in-T∞ :
      formal-disk-at x ≃ formal-disk-at y
    transport-in-T∞ = transport-as-equivalence (T∞-as-dependent-type A) γ

    conclusion = transport-in-T∞


  {-
    most general variant of the triviality theorem
  -}
  module triviality-of-the-formal-disk-bundle-over-homogeneous-types
    {V : 𝒰} (V′ : homogeneous-structure-on V) where

    open homogeneous-structure-on_ V′

    𝔻ₑ = formal-disk-at e
    
    identifications-of-all-formal-disks : (v : V) → 𝔻ₑ ≃ 𝔻 _ v 
    identifications-of-all-formal-disks v =
        paths-induce-equivalences-of-formal-disks.conclusion (is-translation-to v)
      ∘≃
        equivalences-induce-equivalences-on-formal-disks.conclusion (ψ v) e

    as-equivalence-of-dependent-types : equivalence-of (λ _ → 𝔻ₑ) and (λ v → 𝔻 V v) over id
    as-equivalence-of-dependent-types x = identifications-of-all-formal-disks x
    
    T∞V = ∑ (T∞-as-dependent-type V)

    open import HalfAdjointEquivalences

    ha-equivalence-at : (v : V) → 𝔻ₑ ≃ha (𝔻 _ v)
    ha-equivalence-at v = equivalence-to-half-adjoint-equivalence (identifications-of-all-formal-disks v)

    equivalences-as-maps : (x : V) → 𝔻ₑ → 𝔻 _ x
    equivalences-as-maps x =
      underlying-map-of-the-half-adjoint
        (ha-equivalence-at x)

    inverses-as-maps : (x : V) → 𝔻 _ x → 𝔻ₑ
    inverses-as-maps x =
      inverse-of-the-half-adjoint
        (ha-equivalence-at x)

    trivialize : T∞V → V × 𝔻ₑ
    trivialize (v , dv) =
      (v , (inverses-as-maps v) dv)

    trivialize⁻¹ : V × 𝔻ₑ → T∞V
    trivialize⁻¹ (v , dv) =
      (v , equivalences-as-maps v dv) 

    conclusion′ : T∞V ≃ V × 𝔻ₑ
    conclusion′ = trivialize is-an-equivalence-because
      (has-left-inverse trivialize⁻¹
        by (λ {(v , dv) →
           (v , equivalences-as-maps v (inverses-as-maps v dv))
          ≈⟨ (λ d → (v , d)) ⁎ right-invertibility-of-the-half-adjoint (ha-equivalence-at v) dv ⟩
            (v , dv)
          ≈∎})
       and-right-inverse trivialize⁻¹
         by (λ {(v , dv) → (λ d → (v , d)) ⁎ (left-invertibility-of-the-half-adjoint (ha-equivalence-at v) dv ⁻¹)}))

    conclusion  : T∞ V ≃ V × 𝔻ₑ
    conclusion =
        conclusion′
      ∘≃
        pullback-definition-and-dependent-version-agree.conclusion V

    φ = underlying-map-of conclusion

    φ-is-an-equivalence : φ is-an-equivalence
    φ-is-an-equivalence = proof-of-equivalency conclusion

    commutative-triangle : p-of-T∞ V ⇒ π₁ ∘ φ
    commutative-triangle _ = refl

    as-product-square :
      pullback-square-with-right (λ (d : 𝔻ₑ) → ∗)
        bottom (λ (v : V) → ∗)
        top (π₂ ∘ φ)
        left (p-of-T∞ V)
    as-product-square = rotate-cospan
      (substitute-equivalent-cone
        (p-of-T∞ V) (π₂ ∘ φ) φ
        (φ-is-an-equivalence) (λ _ → refl) (λ _ → refl)
        (product-square V 𝔻ₑ))

