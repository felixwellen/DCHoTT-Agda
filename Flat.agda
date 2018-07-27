{-# OPTIONS --without-K #-}

{-
  Learnt about agda-flat from Ian Orton:

  There is a branch of agda called flat, 
  which supports a comonadic modality called flat or ♭

  This file contains some experiments with ♭
  inspired by mike shulmans real-cohesion paper

  Starting with a 'let'-notation I learnd from Ian

  References to Lemmata and Theorems refer to Mike Shulman's Article

  https://arxiv.org/abs/1509.07584

-}


module Flat where
  open import Basics 
  open import EqualityAndPaths
  open import Homotopies
  open import Equivalences
  open import Contractibility
  open import DependentTypes

  data ♭ {l :{♭} Level} (A :{♭} 𝒰 l) : 𝒰 l where
    _^♭ : (a :{♭} A) → ♭ A

  ♭-induction : ∀ {c : Level} {l :{♭} Level}{A :{♭} 𝒰 l}
         → (C : ♭ A → 𝒰 c)
         → ((u :{♭} A) → C (u ^♭))
         → (x : ♭ A) → C x
  ♭-induction C f (x ^♭) = f x

  ♭-counit : ∀ {l :{♭} Level} {A :{♭} 𝒰 l}
    → (♭ A → A)
  ♭-counit (x ^♭) = x

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
      (λ {(x ^♭) → (x ^♭) ^♭})
      by (λ {((x ^♭) ^♭) → refl})
    and-right-inverse
      (λ {(x ^♭) → x ^♭ ^♭})
      by (λ {(x ^♭) → refl})

  let♭ :
    {l l' :{♭} Level}
    {A :{♭} 𝒰 l}
    {C : ♭ A → 𝒰 l'}
    (s : ♭ A)
    (t : (u :{♭} A) → C (u ^♭))
    → -------------
    C s
  let♭ (a ^♭) t = t a

  let♭' :
    {l l' :{♭} Level}
    {A :{♭} 𝒰 l}
    {C : ♭ A → 𝒰 l'}
    (s : ♭ A)
    (t : (u :{♭} A) → C (u ^♭))
    → -------------
    C s
  let♭' {C = C} x t = let♭ {C = C} x t

  syntax let♭ s (λ u → t) = let♭ u ^♭:= s in♭ t
  syntax let♭' {C = C} s (λ u → t) = let♭' u ^♭:= s in♭ t in-family C


  ♭→ : ∀ {A B :{♭} 𝒰₀}
    → (f :{♭} A → B)
    → (♭ A → ♭ B)
  ♭→ f (a ^♭) = (f a) ^♭

  ♭→-commutes-with-∘ : ∀ {A B C :{♭} 𝒰₀}
    → (f :{♭} A → B) (g :{♭} B → C)
    → (♭→ g) ∘ (♭→ f) ⇒ ♭→ (g ∘ f)
  ♭→-commutes-with-∘ f g (a ^♭) = refl


  ♭-identity-induction :
    ∀ {A :{♭} 𝒰₀}
    → (C :{♭} (x y :{♭} A) (p :{♭} x ≈ y) → 𝒰₀)
    → (d :{♭} (x :{♭} A) → C x x refl)
    → (x y :{♭} A) → (p :{♭} x ≈ y) → C x y p
  ♭-identity-induction C d x .x refl = d x


  ♭-preserves-identity-types :
    ∀ {A :{♭} 𝒰₀}
    → (x y :{♭} A)
    → ♭(x ^♭ ≈ y ^♭) ≃ x ≈ y
  ♭-preserves-identity-types x y =
    (λ {(refl ^♭) → refl})
    is-an-equivalence-because
      (has-left-inverse
        (λ {refl → refl ^♭}) by (λ {(refl ^♭)  → refl})
       and-right-inverse
        (λ {refl → refl ^♭}) by (λ {refl → refl})) 

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
    → ♭ (x ≈ y) ≃ x ^♭ ≈ y ^♭
  ♭-commutes-with-identity-types {A} x y =
    let
      {- from Mike's Real-Cohesion Article, section 6 -}
      code : ♭ A → ♭ A → 𝒰₀
      code = λ {(z ^♭) → λ {(w ^♭) → ♭ (z ≈ w) }}

      step1 : code (x ^♭) (y ^♭) ≃ ♭ (x ≈ y)
      step1 = id-as-equivalence

      encode : (u v : ♭ A) → u ≈ v → code u v
      encode u v γ = transport (λ v′ → code u v′)  γ
             ((λ (u : ♭ A) → let♭' x ^♭:= u in♭ (refl ^♭) in-family (λ u′ → code u′ u′)) u)

      decode : (u v : ♭ A) → code u v → u ≈ v
      decode = λ {(x ^♭) (y ^♭) (refl ^♭) → refl }

      step2 : code (x ^♭) (y ^♭) ≃ (x ^♭) ≈ (y ^♭)
      step2 = (decode (x ^♭) (y ^♭))
        is-an-equivalence-because
        ♭-encode-decode-is-enough code encode decode (λ {(x′ ^♭) (y′ ^♭) (refl ^♭) → refl}) (x ^♭) (y ^♭)
    in
      step2 ∘≃ step1


  {- Lemma 6.8 -}

  ♭-commutes-with-Σ :
    ∀ (A :{♭} 𝒰₀) (B :{♭} A → 𝒰₀)
    → ♭ (Σ A B) ≃ Σ (♭ A) (λ x → let♭ u ^♭:= x in♭ ♭ (B u))
  ♭-commutes-with-Σ A B = (λ {((a , b) ^♭) → (a ^♭) , (b ^♭)})
    is-an-equivalence-because
      (has-left-inverse (λ {((a ^♭) , (b ^♭)) → (a , b) ^♭})
         by (λ { ((a , b) ^♭) → refl })
       and-right-inverse (λ {((a ^♭) , (b ^♭)) → (a , b) ^♭})
         by (λ {((a ^♭) , (b ^♭)) → refl }))


  ♭-apply :
    {l :{♭} Level}
    {A B :{♭} 𝒰 l}
    (f :{♭} A → B)
    {x y :{♭} A}
    (p :{♭} x ≈ y)
    → f(x) ≈ f(y)
  ♭-apply f refl = refl


  {- Theorem 6.10 -}

  private 
    glue-equivalences :
      {A : 𝒰₀}
      {P Q : A → 𝒰₀}
      (p : (x : A) → P x ≃ Q x)
      → Σ A P ≃ Σ A Q
    glue-equivalences e =
      fiber-equivalences-along-an-equivalence-on-the-base.induced-map-as-equivalence
        _ _ id-as-equivalence e
    
  ♭-preserves-pullbacks :
    ∀ (A B C :{♭} 𝒰₀) (f :{♭} A → C) (g :{♭} B → C)
    → ♭ (Σ A (λ x → Σ B (λ y → f(x) ≈ g(y))))
      ≃ Σ (♭ A) (λ x → Σ (♭ B) (λ y → (♭→ f)(x) ≈ (♭→ g)(y)))
  ♭-preserves-pullbacks A B C f g =
      ♭ (Σ A (λ x → Σ B (λ y → f(x) ≈ g(y))))
    ≃⟨ ♭-commutes-with-Σ A (λ x → ∑ (λ y → f(x) ≈ g(y))) ⟩
      Σ (♭ A) (λ x → let♭ u ^♭:= x in♭ ♭(Σ B (λ y → f u ≈ g y)))
    ≃⟨ glue-equivalences (λ {(u ^♭) → ♭-commutes-with-Σ B  (λ y → f u ≈ g y)}) ⟩
      Σ (♭ A) (λ x → let♭ u ^♭:= x in♭ (Σ (♭ B) (λ y → let♭ v ^♭:= y in♭ ♭ (f u ≈ g v))))
    ≃⟨ glue-equivalences
         (λ {(u ^♭) → glue-equivalences
           (λ {(v ^♭) → ♭-commutes-with-identity-types (f u) (g v)}) }) ⟩
      Σ (♭ A) (λ x → let♭ u ^♭:= x in♭ (Σ (♭ B) (λ y → let♭ v ^♭:= y in♭ ((f u) ^♭ ≈ (g v) ^♭))))
    ≃⟨ glue-equivalences (λ {(u ^♭) → glue-equivalences (λ {(v ^♭) → id-as-equivalence})}) ⟩
      Σ (♭ A) (λ x → let♭ u ^♭:= x in♭ (Σ (♭ B) (λ y → (f u) ^♭ ≈ (♭→ g) y)))
    ≃⟨ glue-equivalences (λ {(u ^♭) → id-as-equivalence}) ⟩
      Σ (♭ A) (λ x → Σ (♭ B) (λ y → (♭→ f)(x) ≈ (♭→ g)(y)))
    ≃∎

