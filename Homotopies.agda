{-# OPTIONS --without-K #-}

open import Basics public
open import EqualityAndPaths public

module Homotopies where 

-- homotopy
_∼_ : ∀ {i j} {A : U i} {B : U j} → (f g : A → B) → U (i ⊔ j)
_∼_ {i} {j} {A} {B} f g = (a : A) → f a ≈ g a

_⇒_ : ∀ {i j} {A : U i} {B : U j} → (f g : A → B) → U (i ⊔ j)
f ⇒ g = f ∼ g


refl⇒ : ∀ {i} {A B : U i} {f : A → B} → f ⇒ f
refl⇒ a = refl 

id⇒ = refl⇒ 

-- homotopies are natural as morphisms of the induced 
-- functors of path groupoids 
-- f(a) ∼ Ha ∼ g(a)
--  ||          ||
--  fγ          gγ
--  ||          ||
-- f(a′) ∼Ha′∼ g(a)
naturality-of-homotopies : ∀ {A B : U₀} {a a′ : A} (f g : A → B)
                           → (H : f ∼ g) → (γ : a ≈ a′)
                           → H a • g ⁎ γ ≈ f ⁎ γ • H a′
naturality-of-homotopies f g H refl =
                             refl-is-right-neutral (H _) ⁻¹ • refl-is-left-neutral (H _)

conjugate-with-homotopy : 
  ∀ {A B : U₀} {a a′ : A}
  → (f g : A → B) → (H : f ∼ g) → (γ : a ≈ a′)
  → f ⁎ γ ≈ H a • g ⁎ γ • H a′ ⁻¹ 
conjugate-with-homotopy f g H refl =
  ⁻¹-is-right-inversion (H _) ⁻¹
   • (λ ξ → ξ • H _ ⁻¹) ⁎ refl-is-right-neutral (H _)
           


compose-homotopies : ∀ {A B : U₀} {f g h : A → B}
                     → (H : f ⇒ g) (K : g ⇒ h)
                     → f ⇒ h
compose-homotopies H K = λ a → H a • K a


naturality-for-units : ∀ {A B : U₀} (f : A → B) (g : B → A)
                       → (unit :  g ∘ f ∼ id) 
                       → (a : A) → (g ∘ f) ⁎ unit a ≈ unit (g (f a)) 
naturality-for-units f g unit a = (refl-is-right-neutral (unit (g (f a))) •
                                     (λ η → unit ((g ∘ f) a) • η) ⁎ ⁻¹-is-right-inversion (unit a) ⁻¹
                                     • •-is-associative (unit (g (f a))) (unit a) (unit a ⁻¹)
                                     •
                                     (λ η → unit ((g ∘ f) a) • η • unit a ⁻¹) ⁎
                                     id-has-trivial-application (unit a)
                                     ⁻¹
                                     •
                                     (λ η → η • unit a ⁻¹) ⁎
                                     naturality-of-homotopies (g ∘ f) id unit (unit a)
                                     • •-is-associative ((g ∘ f) ⁎ unit a) (unit a) (unit a ⁻¹) ⁻¹
                                     • (λ η → (g ∘ f) ⁎ unit a • η) ⁎ ⁻¹-is-right-inversion (unit a)
                                     • refl-is-right-neutral ((g ∘ f) ⁎ unit a) ⁻¹) ⁻¹

reverse-homotopy : ∀ {i j} {A : U i} {B : U j} {f g : A → B} → f ∼ g → g ∼ f
reverse-homotopy {_} {_} {A} {B} {f} {g} H = λ (a : A) → H a ⁻¹

infix 60 _⁻¹∼
_⁻¹∼ : ∀ {i j} {A : U i} {B : U j} {f g : A → B} → f ∼ g → g ∼ f
H ⁻¹∼ = reverse-homotopy H

infix 60 _⁻¹⇒
_⁻¹⇒ : ∀ {i j} {A : U i} {B : U j} {f g : A → B} → f ⇒ g → g ⇒ f
H ⁻¹⇒ = reverse-homotopy H

-- needs FunExt
--_⁎∼_ : ∀ {i} {A B C D : U i} {f g : A → B} → (F : (A → B) → (C → D)) → f ∼ g → (F f) ∼ (F g)
--F ⁎∼ H = {!!}

-- 2-categorical stuff
_right-whisker_ : ∀ {i} {A B C : U i} {f g : A → B} 
                      → f ⇒ g → (h : B → C) → h ∘ f ⇒ h ∘ g
_right-whisker_ {i} {A} {B} {C} {f} {g} H h = λ (a : A) → h ⁎ H a
_left-whisker_ : ∀ {i j k} {A : U i} {B : U j} {C : U k} {f g : B → C} 
                      →  (h : A → B) → f ⇒ g → f ∘ h ⇒ g ∘ h
_left-whisker_ {i} {_} {_} {A} {B} {C} {f} {g} h H = λ (a : A) → H (h a)

pre-whisker_to_ :
  ∀ {i j k} {A : U i} {B : U j} {C : U k} {f g : B → C} 
  →  (h : A → B) → f ⇒ g → f ∘ h ⇒ g ∘ h
pre-whisker_to_ = _left-whisker_

post-whisker_to_ :
  ∀ {i} {A B C : U i} {f g : A → B} 
  → f ∼ g → (h : B → C) → h ∘ f ⇒ h ∘ g
post-whisker_to_ = _right-whisker_


infixl 50 _•∼_ 
_•∼_ : ∀ {i} {A B : U i} {f g h : A → B} 
      → f ∼ g → g ∼ h → f ∼ h
_•∼_ {i} {A} {B} {f} {g} {h} H-fg H-gh = λ (a : A) → (H-fg a) • (H-gh a)

infixl 50 _∘⇒_ 
_∘⇒_ : ∀ {i} {A B : U i} {f g h : A → B} 
      → g ⇒ h → f ⇒ g → f ⇒ h
H-gh ∘⇒ H-fg = H-fg •∼ H-gh

infixl 50 _•⇒_ 
_•⇒_ : ∀ {i} {A B : U i} {f g h : A → B} 
      → f ⇒ g → g ⇒ h → f ⇒ h
H-fg •⇒ H-gh = H-fg •∼ H-gh

-- reasoning

infix 15 _⇒∎
infixr 10 _⇒-⟨_⟩_

_⇒∎ : ∀ {i} {A B : U i} (f : A → B)
      → f ⇒ f
f ⇒∎ = refl⇒ 

_⇒-⟨_⟩_ : ∀ {i} {A B : U i} (f : A → B) {g h : A → B}
         → f ⇒ g → g ⇒ h → f ⇒ h
f ⇒-⟨ reason ⟩ H = reason •⇒ H
