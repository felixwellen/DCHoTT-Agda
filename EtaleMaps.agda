{-# OPTIONS --without-K #-}

module EtaleMaps where 
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Equivalences hiding (underlying-map-of)
  open import Pullback
  open import PullbackSquare
  open import Im
  open import Language



  -- X --→ ℑ X
  -- |      |
  -- f      |
  -- ↓      ↓
  -- Y --→ ℑ Y
  
  _is-an-étale-map : ∀ {X Y : U₀} (f : X → Y) → U₀ 
  f is-an-étale-map = 
    the-square-given-by-right (apply-ℑ-to-map f) 
      bottom ℑ-unit 
      top ℑ-unit 
      left f 
      commuting-by (naturality-of-ℑ-unit f)
      is-a-pullback-square

  _─ét→_ : (A B : U₀) → U₀
  A ─ét→ B = ∑ (λ (f : A → B) → f is-an-étale-map)

  underlying-map-of : 
    ∀ {A B : U₀}
    → (A ─ét→ B) → (A → B)
  underlying-map-of (f , _) = f


  -- example:
  -- formal disc at a point
  --  
  -- D ---> ∗
  -- | ⌟    |
  -- |      x₀
  -- ↓      ↓
  -- X ---> ℑ X
  D : ∀ (X : U₀) → (x₀ : X) → U₀
  D X x₀ = pullback (λ (x : One) → ℑ-unit x₀) (ℑ-unit-at X)
