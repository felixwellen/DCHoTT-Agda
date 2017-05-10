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
    the-square-with-right (apply-ℑ-to-map f) 
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

  _is-étale = _is-an-étale-map

  pullback-square-for-the-étale-map_ : 
    ∀ {A B : U₀}
    → (f : A ─ét→ B) 
    → pullback-square-with-right (apply-ℑ-to-map (underlying-map-of f)) 
        bottom ℑ-unit 
        top ℑ-unit 
        left (underlying-map-of f)
  pullback-square-for-the-étale-map (f , (the-induced-map-is-an-equivalence-by proof)) = 
    the-square-commuting-by (naturality-of-ℑ-unit f)
    and-inducing-an-equivalence-by proof


  

  -- composition of etale maps
{-
  the-composition-of-the-maps_and_being-étale-by_and_is-étale :
    ∀ {A B C : U₀} 
    → (g : B → C) → (f : A → B) → (g is-étale) → (f is-étale)
    → (g ∘ f) is-étale
  the-composition-of-the-maps g and f being-étale-by g-is-étale and f-is-étale is-étale =
    the-induced-map-is-an-equivalence-by 
      (the-induced-map-in pasted-squares-for-f-and-g is-an-equivalence)
    where pasted-squares-for-f-and-g = {!substitute-homotopic-bottom-map (pasting-of-pullback-squares 
      (rotate-cospan (pullback-square-for-the-étale-map (g , g-is-étale))) 
      (rotate-cospan (pullback-square-for-the-étale-map (f , f-is-étale)))) (ℑ→ (g ∘ f)) ?!}


  infixr 70 _∘ét_
  _∘ét_ : ∀ {A B C : U₀} 
    → (B ─ét→ C) → (A ─ét→ B) → (A ─ét→ C)
  g ∘ét f = {!!}
  
-}
