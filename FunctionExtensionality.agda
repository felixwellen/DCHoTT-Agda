{-# OPTIONS --without-K #-}

module FunctionExtensionality where
  open import Basics
  open import EqualityAndPaths
  open import Equivalences
  open import Homotopies
  open import Interval

  {-
    This approach to function extensionality
    uses an interval, i.e. a higher inductive
    type with two points and one equality between them.
    There is also an approach with univalence, 
    described in the HoTT-Book and implemented in HoTT-Agda.
    Equality of maps 

      f,g : A → B with f ⇒ g

    is shown by constructing first a map

      H : A × I → B

    and applying this to the segment of the interval I.
    This works also for dependent functions.
  -}


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
  
  f-swap : ∀ {A B C : U₀} → (A → B → C) → (B → A → C)
  f-swap f = λ b a → f a b
  
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
{-
  cancel-fun-ext-left : ∀ {A B : U₀} {f g : A → B}
                        → (γ : f ≈ g)
                        → fun-ext (equality-to-homotopy γ) ≈ γ
  cancel-fun-ext-left = {!!} 
-}
  
  mapping-preserves-homotopy :
    ∀ {A B C D : U₀} {f g : A → B} (map : (A → B) → (C → D)) 
    → (H : f ⇒ g) 
    → map f ⇒ map g
  mapping-preserves-homotopy map H = equality-to-homotopy (map ⁎ fun-ext H)

