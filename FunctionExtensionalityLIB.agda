{-# OPTIONS --without-K --rewriting #-}

{- taken from the HoTT-Agda library -}

open import Basics
open import EqualityAndPaths
open import Homotopies
open import Contractibility
open import Equivalences
open import Univalence

{-
A proof of function extensionality from the univalence axiom.
Adapted to this library.
-}

module FunctionExtensionalityLIB {i} {A : 𝒰 i} where

-- Naive non dependent function extensionality

module FunextNonDep {j} {B : 𝒰 j} {f g : A → B} (h : f ⇒ g)
  where

  private
    equiv-comp : {B C : 𝒰 j} (e : B ≃ C)
      →  (λ (g : A → B) → (λ x → e $≃ (g x))) is-an-equivalence
    equiv-comp {B} e =
      equivalence-induction (λ {B} e → (λ (g : A → B) → (λ x → e $≃ (g x))) is-an-equivalence)
                      (λ A' → proof-of-equivalency (id-as-equivalence {_} {A → A'})) e

    free-path-space-B : 𝒰 j
    free-path-space-B = ∑ {A = B} (λ x → ∑ (λ y → x ≈ y))

    d : A → free-path-space-B
    d x = (f x , (f x , refl))

    e : A → free-path-space-B
    e x = (f x , (g x , h x))

    abstract
      fst-is-equiv : (λ (y : free-path-space-B) → ∑π₁ y) is-an-equivalence
      fst-is-equiv = has-inverse (λ _ → _ , (_ , refl)) by
                       (λ a → (λ x → (_ , x)) ⁎
                         contractible-types-are-propositions _ (J-in-terms-of-contractibility′ _ (∑π₁ a)) _ _)
                     and (λ _ → refl) 

      comp-fst-is-equiv : (λ (f : A → free-path-space-B)
                                     → (λ x → ∑π₁ (f x))) is-an-equivalence
      comp-fst-is-equiv = equiv-comp (∑π₁ is-an-equivalence-because fst-is-equiv)

      d≈e : d ≈ e
      d≈e = equivalences-are-injective comp-fst-is-equiv refl

  λ=-nondep : f ≈ g
  λ=-nondep = ap (λ f' x → ∑π₁ (∑π₂ (f' x))) d≈e

open FunextNonDep using (λ=-nondep)

-- Weak function extensionality (a product of contractible types is
-- contractible)
module WeakFunext {j} {P : A → 𝒰 j} (e : (x : A) → (P x) is-contractible) where

  open _is-contractible

  P-is-Unit : P ≈ (λ x → Lift 𝟙)
  P-is-Unit = λ=-nondep (λ x → univalence (contractible-types-are-equivalent-to-the-lift-of-𝟙 (e x)))

  abstract
    weak-λ= : (Π P) is-contractible
    weak-λ= = transport (λ Q → (Π Q) is-contractible) (P-is-Unit ⁻¹)
                            (contracts-to (λ a → lift ∗) by
                            (λ a → λ=-nondep (λ x → contraction 𝟙-is-contractible′ (a x)))) 

-- Naive dependent function extensionality

module FunextDep {j} {P : A → 𝒰 j} {f g : Π P} (h : f ⇒Π g)
  where

  open WeakFunext

  Q : A → 𝒰 j
  Q x = ∑ (λ y → f x ≈ y)

  abstract
    Q-is-contractible : (x : A) → (Q x) is-contractible
    Q-is-contractible x = J-in-terms-of-contractibility′ (P x) (f x)

    instance
      ΠAQ-is-contr : (Π Q) is-contractible
      ΠAQ-is-contr = weak-λ= Q-is-contractible

  Q-f : Π Q
  Q-f x = (f x , refl)

  Q-g : Π Q
  Q-g x = (g x , h x)

  abstract
    Q-f≈Q-g : Q-f ≈ Q-g
    Q-f≈Q-g = contractible-types-are-propositions
              _ ΠAQ-is-contr Q-f Q-g

  λ= : f ≈ g
  λ= = ap (λ u x → ∑π₁ (u x)) Q-f≈Q-g

-- Strong function extensionality

module StrongFunextDep {j} {P : A → 𝒰 j} where

  open FunextDep

  app= : ∀ {f g : Π P} (p : f ≈ g) → f ⇒Π g
  app= p x = ap (λ u → u x) p

  λ=-refl : (f : Π P)
    → refl ≈ λ= (λ x → refl {a = f x})
  λ=-refl f = ap (ap (λ u x → ∑π₁ (u x)))
              (contractible-types-are-propositions
                (Q-f (λ _ → refl) ≈ Q-f (λ _ → refl))
                {!contractible-types-are-propositions _ (ΠAQ-is-contr (λ _ → refl))!}
                refl (Q-f≈Q-g (λ _ → refl)))

  λ=-η : {f g : Π P} (p : f ≈ g)
    → p ≈ λ= (app= p)
  λ=-η {f} refl = λ=-refl f

  app=-β : {f g : Π P} (h : f ⇒Π g) (x : A)
    → app= (λ= h) x ≈ h x
  app=-β h = app=-path (Q-f≈Q-g h) where

    app=-path : {f : Π P} {u v : (x : A) → Q (λ x → refl {a = f x}) x}
      (p : u ≈ v) (x : A)
      → app= (ap (λ u x → ∑π₁ (u x)) p) x ≈ ((∑π₂ (u x)) ⁻¹) • ∑π₂ (v x)
    app=-path {u = u} refl x = (⁻¹-is-left-inversion (∑π₂ (u x))) ⁻¹

  app=-is-equiv : {f g : Π P} → (app= {f = f} {g = g}) is-an-equivalence
  app=-is-equiv = has-inverse λ= by {!!} and {!!}  --  (λ h → λ= (app=-β ?)) (((λ γ → γ ⁻¹) ∘ λ=-η))

  λ=-is-equiv : {f g : Π P}
    → (λ= {f = f} {g = g}) is-an-equivalence
  λ=-is-equiv = has-inverse app= by (λ h → λ= (app=-β h)) and {!((λ γ → γ ⁻¹) ∘ λ=-η) !} -- 

-- We only export the following

module _ {j} {P : A → 𝒰 j} {f g : Π P} where

  app= : f ≈ g → f ⇒Π g
  app= p x = ap (λ u → u x) p

  abstract
    λ= : f ⇒Π g → f ≈ g
    λ= = FunextDep.λ=

    app=-β : (p : f ⇒Π g) (x : A) → app= (λ= p) x ≈ p x
    app=-β = StrongFunextDep.app=-β

    λ=-η : (p : f ≈ g) → p ≈ λ= (app= p)
    λ=-η = StrongFunextDep.λ=-η

  λ=-equiv : (f ⇒Π g) ≃ (f ≈ g)
  λ=-equiv = λ= is-an-equivalence-because λ=-is-equiv where
    abstract
      λ=-is-equiv : λ= is-an-equivalence
      λ=-is-equiv = StrongFunextDep.λ=-is-equiv

  app=-equiv : (f ≈ g) ≃ (f ⇒Π g)
  app=-equiv = app= is-an-equivalence-because app=-is-equiv where
    abstract
      app=-is-equiv : app= is-an-equivalence
      app=-is-equiv = StrongFunextDep.app=-is-equiv
