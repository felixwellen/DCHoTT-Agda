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
  open import Contractibility
  open import DependentTypes

  data ♭ {l :{♭} Level} (A :{♭} 𝒰 l) : 𝒰 l where
    con : (a :{♭} A) → ♭ A

  ♭-induction : ∀ {c : Level} {l :{♭} Level}{A :{♭} 𝒰 l}
         → (C : ♭ A → 𝒰 c)
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

  ♭-counit : ∀ {l :{♭} Level} {A :{♭} 𝒰 l}
    → (♭ A → A)
  ♭-counit (con x) = x

  ♭-counit-at : 
      ∀ (A :{♭} 𝒰₀)
    → (♭ A → A)
  ♭-counit-at A = ♭-counit {_} {A}

  _is-discrete : ∀ (A :{♭} 𝒰₀) → 𝒰₀
  A is-discrete = (♭-counit-at A) is-an-equivalence

  ♭-idempotent : ∀ (A :{♭} 𝒰₀)
    → (♭ A) is-discrete
  ♭-idempotent A =
    has-left-inverse
      (λ {(con x) → con (con x)})
      by (λ {(con (con x)) → refl})
    and-right-inverse
      (λ {(con x) → con (con x)})
      by (λ {(con x) → refl})

  ♭-uniqueness :
    ∀ {A :{♭} 𝒰₀}
      {C : ♭ A → 𝒰₀}
      (f : (x : ♭ A) → C x)
    → 
      (x : ♭ A) → (let♭ u := x in♭ f (con u) in-family C)  ≈ f(x)
  ♭-uniqueness f (con a) = refl


  ♭→′ : ∀ {A B :{♭} 𝒰₀}
    → (f :{♭} A → B)
    → (♭ A → ♭ B)
  ♭→′ {_} {B} f x = let♭ u := x in♭ con (f u) in-family (λ _ → ♭ B)
  
  ♭→ : ∀ {A B :{♭} 𝒰₀}
    → (f :{♭} A → B)
    → (♭ A → ♭ B)
  ♭→ f (con a) = con (f a)

  ♭→≈♭→′ : ∀ {A B :{♭} 𝒰₀}
    → (f :{♭} A → B)
    → (x : ♭ A) → (♭→ f) x ≈ (♭→′ f) x
  ♭→≈♭→′ f (con a) = refl

  ♭→-commutes-with-∘ : ∀ {A B C :{♭} 𝒰₀}
    → (f :{♭} A → B) (g :{♭} B → C)
    → (♭→ g) ∘ (♭→ f) ⇒ ♭→ (g ∘ f)
  ♭→-commutes-with-∘ f g (con a) = refl


  ♭-identity-induction :
    ∀ {A :{♭} 𝒰₀}
    → (C :{♭} (x y :{♭} A) (p :{♭} x ≈ y) → 𝒰₀)
    → (d :{♭} (x :{♭} A) → C x x refl)
    → (x y :{♭} A) → (p :{♭} x ≈ y) → C x y p
  ♭-identity-induction C d x .x refl = d x


  ♭-preserves-identity-types :
    ∀ {A :{♭} 𝒰₀}
    → (x y :{♭} A)
    → ♭(con x ≈ con y) ≃ x ≈ y
  ♭-preserves-identity-types x y =
    (λ {(con refl) → refl})
    is-an-equivalence-because
      (has-left-inverse
        (λ {refl → con refl}) by (λ {(con refl)  → refl})
       and-right-inverse
        (λ {refl → con refl}) by (λ {refl → refl})) 

  ♭-encode-decode-is-enough :
    ∀ {A :{♭} 𝒰₀} (code : ♭ A → ♭ A → 𝒰₀)
    → (encode : (x y : ♭ A) → x ≈ y → code x y)
    → (decode : (x y : ♭ A) → code x y → x ≈ y)
    → (retract : (x y : ♭ A) → (encode x y) ∘ (decode x y) ⇒ id)
    → (x y : ♭ A) → (decode x y) is-an-equivalence
  ♭-encode-decode-is-enough {A} code encode decode retract x y =
    let
      step1 : (z : ♭ A) → (∑ (λ w → code z w)) is-contractible
      step1 z = retracts-of-contractibles-are-contractible
        (λ {(w , c) → (w , decode z w c)})
        (λ {(w , γ) → (w , encode z w γ)})
        (λ {(w , c) → (inclusion-of-the-fiber-of _ over w) ⁎ retract z w c})
        (J-in-terms-of-contractibility′ (♭ A) z)

      step2 : (z : ♭ A) → (λ {(w , c) → (w , decode z w c)}) is-an-equivalence
      step2 z = the-map (λ {(w , c) → (w , decode z w c)}) is-an-equivalence-since-it-is-homotopic-to
        _ by
             maps-into-a-contractible-type-are-homotopic
               _ _ ((J-in-terms-of-contractibility′ (♭ A) z))
          which-is-an-equivalence-by
          (proof-of-equivalency (two-contractible-types-are-equivalent
            (step1 z) (J-in-terms-of-contractibility′ (♭ A) z) ))


    in equivalence-from-equivalence-on-sums.conclusion (decode x) (step2 x) y

  ♭-commutes-with-identity-types :
    ∀ {A :{♭} 𝒰₀}
    → (x y :{♭} A)
    → ♭ (x ≈ y) ≃ con x ≈ con y 
  ♭-commutes-with-identity-types {A} x y =
    let
      -- from Mike's Real-Cohesion Article, section 6
      code : ♭ A → ♭ A → 𝒰₀
      code = λ {(con z) → λ {(con w) → ♭ (z ≈ w) }}

      step1 : code (con x) (con y) ≃ ♭ (x ≈ y)
      step1 = id-as-equivalence

      encode : (u v : ♭ A) → u ≈ v → code u v
      encode u v γ = transport (λ v′ → code u v′)  γ
             ((λ (u : ♭ A) → let♭ x := u in♭ (con refl) in-family (λ u′ → code u′ u′)) u)

      decode : (u v : ♭ A) → code u v → u ≈ v
      decode = λ {(con x) (con y) (con refl) → refl }

      step2 : code (con x) (con y) ≃ (con x) ≈ (con y)
      step2 = (decode (con x) (con y))
        is-an-equivalence-because
        ♭-encode-decode-is-enough code encode decode (λ {(con x′) (con y′) (con refl) → refl}) (con x) (con y)
    in
      step2 ∘≃ step1
