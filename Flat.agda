{-# OPTIONS --without-K #-}

{-
  Learnt about agda-flat from Ian Orton:

  There is a branch of agda called flat, 
  which supports a comonadic modality called flat or ♭

  This file contains some experiments with ♭
  inspired by mike shulmans real-cohesion paper

  Starting with a 'let'-notation I learnd from Ian
-}


module Flat where
  open import Basics 
  open import EqualityAndPaths
  open import Homotopies
  open import Equivalences

  data ♭ {l :{♭} Level} (A :{♭} 𝒰- l) : 𝒰- l where
    con : (a :{♭} A) → ♭ A

  ♭-induction : ∀ {c : Level} {l :{♭} Level}{A :{♭} 𝒰- l}
         → (C : ♭ A → 𝒰- c)
         → ((u :{♭} A) → C (con u))
         → (x : ♭ A) → C x
  ♭-induction C f (con x) = f x

  let♭ :
    {A :{♭} Set}
    {C : ♭ A → Set}
    (s : ♭ A)
    (t : (u :{♭} A) → C (con u))
    → -------------
    C s
  let♭ (con a) t = t a

--  syntax let♭ s (λ u → t) = let♭ u := s in♭ t
  
  syntax let♭ {C = C} s (λ u → t) = let♭ u := s in♭ t in-family C

  ♭-counit : ∀ {l :{♭} Level} {A :{♭} 𝒰- l}
    → (♭ A → A)
  ♭-counit (con x) = x

  ♭-counit-at : 
      ∀ (A :{♭} 𝒰)
    → (♭ A → A)
  ♭-counit-at A = ♭-counit {_} {A}

  _is-discrete : ∀ (A :{♭} 𝒰) → 𝒰
  A is-discrete = (♭-counit-at A) is-an-equivalence

  ♭-idempotent : ∀ (A :{♭} 𝒰)
    → (♭ A) is-discrete
  ♭-idempotent A =
    has-left-inverse
      (λ {(con x) → con (con x)})
      by (λ {(con (con x)) → refl})
    and-right-inverse
      (λ {(con x) → con (con x)})
      by (λ {(con x) → refl})

  ♭-uniqueness :
    ∀ {A :{♭} 𝒰}
      {C : ♭ A → 𝒰}
      (f : (x : ♭ A) → C x)
    → 
      (x : ♭ A) → (let♭ u := x in♭ f (con u) in-family C)  ≈ f(x)
  ♭-uniqueness f (con a) = refl


  ♭→′ : ∀ {A B :{♭} 𝒰}
    → (f :{♭} A → B)
    → (♭ A → ♭ B)
  ♭→′ {_} {B} f x = let♭ u := x in♭ con (f u) in-family (λ _ → ♭ B)
  
  ♭→ : ∀ {A B :{♭} 𝒰}
    → (f :{♭} A → B)
    → (♭ A → ♭ B)
  ♭→ f (con a) = con (f a)

  ♭→≈♭→′ : ∀ {A B :{♭} 𝒰}
    → (f :{♭} A → B)
    → (x : ♭ A) → (♭→ f) x ≈ (♭→′ f) x
  ♭→≈♭→′ f (con a) = refl

  ♭→-commutes-with-∘ : ∀ {A B C :{♭} 𝒰}
    → (f :{♭} A → B) (g :{♭} B → C)
    → (♭→ g) ∘ (♭→ f) ⇒ ♭→ (g ∘ f)
  ♭→-commutes-with-∘ f g (con a) = refl

  ♭-preserves-identity-types :
    ∀ {A :{♭} 𝒰}
    → (x y :{♭} A)
    → ♭(con x ≈ con y) ≃ x ≈ y
  ♭-preserves-identity-types x y =
    (λ {(con refl) → refl})
    is-an-equivalence-because
      (has-left-inverse
        (λ {refl → con refl}) by (λ {(con refl)  → refl})
       and-right-inverse
        (λ {refl → con refl}) by (λ {refl → refl})) 
