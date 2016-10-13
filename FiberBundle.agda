{-# OPTIONS --without-K #-}

module FiberBundle where 
  open import Basics 
  open import EqualityAndPaths
  open import PropositionalTruncation
  open import PullbackSquare
  open import Homotopies
  open import Im
  open import FormalDiskBundle
  open import EtaleMaps
  open import Language
  open import OneImage
  open import DependentTypes
  open import InfinityGroups


  -- product property expressed by pullback square
  _is-a-product-with-projections_and_ :
    ∀ {A B : U₀} (Z : U₀) (z₁ : Z → A) (z₂ : Z → B)
    → U₀
  Z is-a-product-with-projections z₁ and z₂ =
    pullback-square-with-right (λ a → ∗)
        bottom (λ b → ∗)
        top z₁
        left z₂

  _is-a-product-of_and_ :
    (Z A B : U₀) → U₀
  Z is-a-product-of A and B =
    ∑ (λ (z₁ : Z → A) →
    ∑ (λ (z₂ : Z → B) → Z is-a-product-with-projections z₁ and z₂))

  _*_ : ∀ {E B B′ : U₀}
    → (f : B′ → B) → (φ : E → B) → U₀
  f * φ = upper-left-vertex-of (complete-to-pullback-square φ f)
  
  _*→_ : ∀ {E B B′ : U₀}
    → (f : B′ → B) → (φ : E → B) → ((f * φ) → B′)
  f *→ φ = left-map-of (complete-to-pullback-square φ f)

  ^ = underlying-map-of-the-surjectiveism


  {- 
    a fiber bundle φ : E → B is required locally trivial, 
    which might be witnessed by a pullback square like this:

    V×F ───→ E
     | ⌟     |
    v*φ      φ
     ↓       ↓
     V ──v─↠ B
     
  -}

  record _is-a_-fiber-bundle {E B : U₀} (φ : E → B) (F : U₀) : U₁ where
    constructor on_the-pullback-along_is-trivial-by_and_
    field
      V : U₀
      covering : V ↠ B
      projection-to-the-fiber : (^ covering * φ) → F
      the-pullback-is-a-product :
          (^ covering * φ) is-a-product-with-projections
            projection-to-the-fiber and (^ covering *→ φ) 

  covering-as-map : 
    ∀ {E B F : U₀} {φ : E → B} (φ-as-bundle : φ is-a F -fiber-bundle)
    → _is-a_-fiber-bundle.V φ-as-bundle → B
  covering-as-map φ-as-bundle = ^ (_is-a_-fiber-bundle.covering φ-as-bundle)

  -- project to the square drawn in the comment above
  covering-pullback-square :
    ∀ {E B F : U₀} {φ : E → B} (φ-as-bundle : φ is-a F -fiber-bundle)
    → pullback-square-with-right φ
       bottom (covering-as-map φ-as-bundle)
       top _
       left (((covering-as-map φ-as-bundle) *→ φ))
  covering-pullback-square {_} {_} {_} {φ} φ-as-bundle = 
    complete-to-pullback-square φ (covering-as-map φ-as-bundle) 


  module all-fiber-bundle-are-associated
          {E B F : U₀} (φ : E → B) (φ-is-a-fiber-bundle : φ is-a F -fiber-bundle) where
         
         {-

           take the pullback-square witnessing the local triviality of φ
    
           v*E ───→ E
            | ⌟     |
           v*φ      φ
            ↓       ↓
            V ──v─↠ B
         
         -}

         open _is-a_-fiber-bundle φ-is-a-fiber-bundle

         v = covering-as-map φ-is-a-fiber-bundle
         v*φ = v *→ φ 

         covering-square : 
           pullback-square-with-right φ
             bottom v
             top _
             left v*φ
         covering-square = 
           covering-pullback-square φ-is-a-fiber-bundle
             
         {-

           ... and the product square for v*E:
    
           v*E ─p─→ F
            | ⌟     |
           v*φ      |
            ↓       ↓
            V ────→ 1
     
         -}
         
         v*E = v * φ
         p : v*E → F
         p = projection-to-the-fiber

         product-square-for-v*E = the-pullback-is-a-product

         {- 
           switch to classifying maps, i.e. get:

           1 ←─ V ─→ B
            \   |   /
             \  |  /
              ↘ ↓ ↙ 
                U
         -}

         left-triangle : dependent-replacement v*φ ⇒ dependent-replacement (λ (x : F) → ∗) ∘ (λ (x : V) → ∗)
         left-triangle = 
           pullbacks-are-fiberwise-equivalences.as-triangle-over-the-universe 
             product-square-for-v*E

         right-triangle : dependent-replacement v*φ ⇒ dependent-replacement φ ∘ v
         right-triangle = 
           pullbacks-are-fiberwise-equivalences.as-triangle-over-the-universe 
             covering-square

         {-
           conclude that 'v*φ' factors over the point
         -}

