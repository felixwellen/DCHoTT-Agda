{-# OPTIONS --without-K #-}

module FirstOrderDisks where 
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Language
  open import Equivalences
  open import CommonEquivalences  
  open import Pullback
  open import PullbackSquare
  open import Im
  open import Im1
  open import DependentTypes
  open import FormalDiskBundle


  -- we will now introduce first order infinitesimals
  -- they will be needed to define torsion-freeness
  -- of G-structures

  _is-first-order-infinitesimally-close-to_ :
    {X : U₀} → (x x′ : X) → U₀
  x is-first-order-infinitesimally-close-to x′ = ℑ₁-unit x ≈ ℑ₁-unit x′

  _is-1-close-to_ = _is-first-order-infinitesimally-close-to_

  first-order-disk-at_ :
    ∀ {X : U₀}
    → (x : X) → U₀
  first-order-disk-at x =
    ∑ (λ x′ → x is-first-order-infinitesimally-close-to x′)

  -- relate inf-close to first-order-close
  map-to-coreduction :
    ∀ {A : U₀}
    → ℑ₁ A → ℑ A
  map-to-coreduction {A} =
    ℑ₁-recursion
      (coreduced-types-are-1-coreduced (ℑ-is-coreduced A))
      (ℑ-unit-at A)

  map-to-coreduction-commutes-with-units :
    ∀ {A : U₀}
    → map-to-coreduction ∘ (ℑ₁-unit-at A) ⇒ (ℑ-unit-at A)
  map-to-coreduction-commutes-with-units a =
    ℑ₁-compute-recursion (coreduced-types-are-1-coreduced (ℑ-is-coreduced _)) (ℑ-unit-at _) a
  
  first-order-proximity-implies-general-proximity :
    ∀ {A : U₀} {x y : A}
    → x is-first-order-infinitesimally-close-to y → x is-close-to y
  first-order-proximity-implies-general-proximity γ =
      map-to-coreduction-commutes-with-units _ ⁻¹
    • map-to-coreduction ⁎ γ
    • map-to-coreduction-commutes-with-units _

  -- this is just repeatition of FormalDiskBundle.agda:
  mapping-with_preserves-1-proximity :
    ∀ {X Y : U₀} {x x′ : X}
    → (f : X → Y)
    → (x is-1-close-to x′) → (f x) is-1-close-to (f x′)
  mapping-with f preserves-1-proximity γ = ℑ₁⁎ f ⁎ γ  -- see 'Im1.agda'

  induced-map-on-first-order-disks :
    ∀ {X Y : U₀}
    → (f : X → Y)
    → (x : X) → first-order-disk-at x → first-order-disk-at (f x)
  induced-map-on-first-order-disks f x (x′ , x′-is-1-close-to-x) =
    (f x′ , mapping-with f preserves-1-proximity x′-is-1-close-to-x)
  --

  inclusion-of-disks :
    ∀ {A : U₀} (x : A)
    → first-order-disk-at x → formal-disk-at x
  inclusion-of-disks x (a , γ) = (a , (first-order-proximity-implies-general-proximity γ))

{-
  inlcusion-commutes-with-induced-maps :
    ∀ {A B : U₀}
    → (f : A → B)
    → (x : A)
    → (induced-map-on-formal-disks f x) ∘ (inclusion-of-disks x)
     ⇒ (inclusion-of-disks (f x)) ∘ (induced-map-on-first-order-disks f x)
  inlcusion-commutes-with-induced-maps f x = {!!}
-}
