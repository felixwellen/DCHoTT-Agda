{-# OPTIONS --without-K #-}

module OneImage where 
  open import Basics 
  open import EqualityAndPaths
  open import PropositionalTruncation

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
  the-induced-map-from-the-1-image-of f to-the-codomain (above b is x) = b
  
  ι-im₁ = the-induced-map-from-the-1-image-of_to-the-codomain

  the-induced-map-from-the-domain-to-the-1-image-of :
    ∀ {A B : U₀} 
    → (f : A → B) → (A → 1-image f)
  the-induced-map-from-the-domain-to-the-1-image-of f a = 
    ⟨ f(a) , ∣ ⟨ a , refl ⟩∑ ∣ ⟩∑

  π-im₁ = the-induced-map-from-the-domain-to-the-1-image-of

  _is-monomorph : 
    ∀ {A B : U₀} 
    → (f : A → B) → U₀
  f is-monomorph = (x y : _) → f x ≈ f y → x ≈ y
  
  ι-im₁-is-monomorph : 
    ∀ {A B : U₀}
    → (f : A → B)
    → (ι-im₁ f) is-monomorph
  ι-im₁-is-monomorph f (above b is b-is-in-the-image)
                       (above b′ is b′-is-in-the-image) γ
     = let b≈b′ = b ≈⟨ γ ⟩ b′ ≈∎
       in {!apd (λ b → the-1-image-of f contains b)!}
