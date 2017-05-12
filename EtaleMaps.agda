{-# OPTIONS --without-K #-}

module EtaleMaps where 
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Equivalences renaming (underlying-map-of to underlying-map-of-the-equivalence)
  open import Pullback
  open import PullbackSquare
  open import DependentTypes
  open import Im
  open import Language

  _as-plain-map :
    ∀ {A B : U₀}
    → (f : A ≃ B) → (A → B)
  f as-plain-map = underlying-map-of-the-equivalence f 

  -- X --→ ℑ X
  -- |      |
  -- f      ℑf
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

  -- this also follows from stuff in the proof of the triviality theorem
  equivalences-are-étale :
    ∀ {A B : U₀} (f : A ≃ B)
    → (f as-plain-map) is-an-étale-map
  equivalences-are-étale {A} {B} f =
    let
      □ : pullback-square-with-right ℑ→ (f as-plain-map)
            bottom ℑ-unit
            top ℑ-unit
            left (f as-plain-map)
      □ = pullback-preserves-equivalences.reverse-statement
           (ℑ→ (f as-plain-map))
           ℑ-unit (applying-ℑ-preserves-equivalences (f as-plain-map) (proof-of-equivalency f) )
           ℑ-unit
           (f as-plain-map) (naturality-of-ℑ-unit (f as-plain-map))
           (proof-of-equivalency f)
    in the-induced-map-is-an-equivalence-by
     (the-induced-map-in □ is-an-equivalence)


  _─ét→_ : (A B : U₀) → U₀
  A ─ét→ B = ∑ (λ (f : A → B) → f is-an-étale-map)

  id-as-étale-map :
    ∀ {A : U₀}
    → A ─ét→ A
  id-as-étale-map = (id , equivalences-are-étale id-as-equivalence)

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
