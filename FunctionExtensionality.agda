{-# OPTIONS --without-K #-}

module FunctionExtensionality where
  open import Basics
  open import EqualityAndPaths
  open import Equivalences
  open import Homotopies
  open import Interval


  function-extensionality : ∀ {i j} (A : U i) (P : A → U j)
                            → (f g : (a : A) → P a)
                            → ((a : A) → f(a) ≈ g(a)) → f ≈ g
  function-extensionality A P f g f∼g = 
                          let H : (a : A) → I → P a
                              H a = I-recursion (f a) (g a) (f∼g a)
                          in (λ i a → H a i) ⁎ seg
  
  fun-ext : ∀ {i j} {A : U i} {P : A → U j}
              → {f g : (a : A) → P a}
              → ((a : A) → f(a) ≈ g(a)) → f ≈ g
  fun-ext = function-extensionality _ _ _ _
  
  equality-to-homotopy : ∀ {i} {A B : U i} {f g : A → B}
                         → f ≈ g → (a : A) → f a ≈ g a
  equality-to-homotopy refl a = refl
  
  equality-to-homotopy′ : ∀ {A B : U₀} {f g : A → B}
                        → f ≈ g → (a : A) → f a ≈ g a
  equality-to-homotopy′ γ a = (λ f → f a) ⁎ γ
  
  those-are-equal : ∀ {A B : U₀} {f g : A → B}
                    → (γ : f ≈ g) → (a : A)
                    → equality-to-homotopy γ a ≈ equality-to-homotopy′ γ a
  those-are-equal refl a = refl                  
  
  f-swap : ∀ {A B C : U₀} → (A → B → C) → (B → A → C)
  f-swap f = λ b a → f a b
  -- _ ⁎ _ : (f : A → B → C) → x ≈A y → f(x) ≈B→C f(y)
  -- _ ⁎ _ : (f : B → A → C) → x ≈B y → f(x) ≈A→C f(y)
  -- _ ⁎ _ : (f : A × B → C) → x ≈A×B y → f(x) ≈C f(y)
  
  cancel-fun-ext′ : ∀ {A B : U₀} (f g : A → B)
                  → (H : (a : A) → f(a) ≈ g(a))
                  → (a : A) → equality-to-homotopy′ (fun-ext H) a ≈ H a
  cancel-fun-ext′ f g H a = 
    apply-commutes-with-evaluation seg a
                               (λ i a₁ → I-recursion (f a₁) (g a₁) (H a₁) i)
                               • uniqueness-of-I-recursion (f a) (g a) (H a)

  cancel-fun-ext : ∀ {A B : U₀} {f g : A → B}
                   → (H : (a : A) → f(a) ≈ g(a))
                   → (a : A) → equality-to-homotopy (fun-ext H) a ≈ H a
  cancel-fun-ext H a = those-are-equal (fun-ext H) a
                       • (cancel-fun-ext′ _ _ H a)

  mapping-preserves-homotopy : ∀ {A B C D : U₀} {f g : A → B} (map : (A → B) → (C → D)) 
                               → (H : f ⇒ g) 
                               → map f ⇒ map g
  mapping-preserves-homotopy map H = equality-to-homotopy (map ⁎ fun-ext H)

