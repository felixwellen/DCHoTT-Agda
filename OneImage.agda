{-# OPTIONS --without-K #-}

module OneImage where 
  open import Basics 
  open import EqualityAndPaths
  open import Homotopies
  open import Equivalences
  open import Contractibility
  open import PropositionalTruncation

  -- the following is called 'surjective' in the HoTT-Book
  _is-surjective : 
    ∀ {A B : U₀}
    → (A → B) → U₀
  _is-surjective {A} {B} f = Π (λ (b : B) → ∥ fiber-of f at b ∥)

  record _↠_ (A B : U₀) : U₁ where
    constructor _is-surjective-by_
    field
      morphism : A → B
      proof-that-it-is-surjective : morphism is-surjective

  underlying-map-of-the-surjectiveism : 
    ∀ {A B : U₀}
    → (f : A ↠ B) → (A → B)
  underlying-map-of-the-surjectiveism
    (morphism is-surjective-by proof-that-it-is-surjective) = morphism

  the-1-image-of_contains : 
    ∀ {A B : U₀} 
    → (f : A → B) → (B → U₀)
  the-1-image-of f contains b = ∥ ∑ (λ a → f(a) ≈ b) ∥

  1-image :
    ∀ {A B : U₀} 
    → (f : A → B) → U₀
  1-image f = ∑ (λ b → the-1-image-of f contains b)

  im₁ = 1-image

  the-induced-map-from-the-1-image-of_to-the-codomain :
    ∀ {A B : U₀} 
    → (f : A → B) → (1-image f → B)
  the-induced-map-from-the-1-image-of f to-the-codomain (b , x) = b
  
  ι-im₁ = the-induced-map-from-the-1-image-of_to-the-codomain

  the-induced-map-from-the-domain-to-the-1-image-of :
    ∀ {A B : U₀} 
    → (f : A → B) → (A → 1-image f)
  the-induced-map-from-the-domain-to-the-1-image-of f a = 
    (f(a) , ∣ (a , refl ) ∣ )

  π-im₁ = the-induced-map-from-the-domain-to-the-1-image-of

  _is-injective : 
    ∀ {A B : U₀} 
    → (f : A → B) → U₀
  f is-injective = (x y : _) → f x ≈ f y → x ≈ y

  _is-injective′ : 
    ∀ {A B : U₀} 
    → (f : A → B) → U₀
  f is-injective′ = Π (λ b → (fiber-of f at b) is-a-proposition)

{-
  compatibility :
    ∀ {A B : U₀} 
    → (f : A → B)
    → f is-injective → f is-injective′
  compatibility f f-is-injective b (a is-in-the-fiber-by γ) (a′ is-in-the-fiber-by η) = {!f-is-injective a a′ (γ • η ⁻¹)!}
-}  

  a-injectiveism-factoring-over-the-point-is-trivial :
    ∀ {A B : U₀} (f : A → B)
    → (f is-injective)
    → ∑ (λ b → f ⇒ (λ _ → b))
    → A is-a-proposition
  a-injectiveism-factoring-over-the-point-is-trivial f f-is-mono (b , H) =
    λ a a′ → f-is-mono a a′ (H a • H a′ ⁻¹)
{-
  ι-im₁-is-injective : 
    ∀ {A B : U₀}
    → (f : A → B)
    → (ι-im₁ f) is-injective
  ι-im₁-is-injective f (b , b-is-in-the-image)
                       (b′ , b′-is-in-the-image) γ
     = let b≈b′ = b ≈⟨ γ ⟩ b′ ≈∎
       in {!apd (λ b → the-1-image-of f contains b)!}
-}


{-
   injective/surjective lifting
   
   given a commutative square:
     
     A ─f─→ X
     |      |
     e      m
     ↓      ↓
     B ─g─→ Y
   
   with m injective and e surjective there should be a 
   diagonal lift...
-}

  module injective/surjective-lifting
         {A B X Y : U₀} 
         (m : X → Y) (g : B → Y)
         (f : A → X) (e : A → B)
         (m-is-injective : m is-injective′) (e-is-surjective : e is-surjective)
         (H : m ∘ f ⇒ g ∘ e)
         where
    {- idea: take a 'b : B' and map it to x in the 
             propositional truncation of the fiber 
             over b, given by the assumption that 
             e is surjective. map x to the fiber over
             g(b), which is possible because m is 
             injective.
    -}
    map-to-the-fiber : (b : B) → fiber-of e at b → fiber-of m at g(b)
    map-to-the-fiber b = λ {(a is-in-the-fiber-by γ) → f(a) is-in-the-fiber-by (H a • g ⁎ γ)}
    induced-map-on-the-truncated-fiber : (b : B) → ∥ fiber-of e at b ∥ → fiber-of m at g(b)
    induced-map-on-the-truncated-fiber b = 
        ∥-∥-recursion 
          (fiber-of m at g(b)) 
          (m-is-injective (g b)) 
          (map-to-the-fiber b) 
    lift : (B → X)
    lift b = as-point-in-the-domain (induced-map-on-the-truncated-fiber b (e-is-surjective b))
  
    upper-triangle : f ⇒ lift ∘ e 
    upper-triangle a = {!!}
   
    lower-triangle : m ∘ lift ⇒ g
    lower-triangle b = {!!}
