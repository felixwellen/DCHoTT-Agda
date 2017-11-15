{-# OPTIONS --without-K #-}

module Basics where

-- if your agda version is < 2.4 you might have to use the following:
-- 
-- postulate  -- Universe levels
--   Level : Set
--   lzero : Level
--   lsuc : Level → Level
--   _⊔_ : Level → Level → Level
-- 
-- {-# BUILTIN LEVEL Level #-}
-- {-# BUILTIN LEVELZERO lzero #-}
-- {-# BUILTIN LEVELSUC lsuc #-}
-- {-# BUILTIN LEVELMAX _⊔_ #-}
-- 
-- instead of this line:
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public

U : (i : Level) → Set (lsuc i)
U i = Set i


U₀ = U lzero
U₁ = U (lsuc lzero)


-- supposed to be standard names in the future:
𝒰 = U₀
𝒰₀ = U₀
𝒰₁ = U₁

domain : ∀ {A B : U₀} → (A → B) → U₀
domain {A} {_} _ = A

codomain : ∀ {A B : U₀} → (A → B) → U₀
codomain {_} {B} _ = B


data Bool : Set where
  true : Bool
  false : Bool


Π : ∀ {i j} → {A : U i} → (P : A → U j) → U (i ⊔ j)
Π {_} {_} {A} P = (a : A) → P a

π-Π : ∀ {A : U₀} {P : A → U₀}
      → (a : A) → Π P → P a
π-Π a = λ s → s a      

infix 20 _,_
record ∑ {i j} {A : U i} (P : A → U j) : U (i ⊔ j) where
  constructor _,_
  field
    a : A
    p : P a

ι-∑ : ∀ {i} {j} {A : U i} {P : A → U j}
      → (a : A) → P a → ∑ P
ι-∑ a p = (a , p)


∑π₁ : ∀ {i} {j} {A : U i} {P : A → U j} 
  → ∑ P → A
∑π₁ (a , _) = a

∑π₁-from_ :
  ∀ {i} {j} {A : U i} (P : A → U j)
  → ∑ P → A
∑π₁-from P = ∑π₁

∑π₂ : ∀ {i} {j} {A : U i} {P : A → U j}
  → (x : ∑ P) → P (∑π₁ x)
∑π₂ (a , p) = p  

∑π₂-from_ :
  ∀ {i} {j} {A : U i} (P : A → U j)
  → (x : ∑ P) → P (∑π₁ x)
∑π₂-from P = ∑π₂

Π-to-∑ : ∀ {A : U₀} {P : A → U₀}
         → Π P → A → ∑ P
Π-to-∑ s a = (a , s a)

infix 60 _×_

_×_ : 
  ∀ {i j} 
  → (A : U i) → (B : U j) → U (i ⊔ j)
A × B = ∑ (λ (a : A) → B)

_×→_ : ∀ {A B A′ B′ : U₀} → (A → B) → (A′ → B′) → (A × A′ → B × B′)
f ×→ g = λ { (a , b) → f a , g b }

_,→_ : ∀ {X A B : U₀} → (X → A) → (X → B) → (X → A × B)
f ,→ g = λ x → (f x , g x)

π₁ : ∀ {i} {A : U i} {B : U i} → A × B → A
π₁ (a , b) = a

π₂ : ∀ {i} {A : U i} {B : U i} → A × B → B
π₂ (a , b) = b 


π₁-from_×_ : ∀ {i} (A : U i) (B : U i) → A × B → A
π₁-from A × B = π₁

π₂-from_×_ : ∀ {i} (A : U i) (B : U i) → A × B → B
π₂-from A × B = π₂

Δ : ∀ {A : U₀}
    → A → A × A
Δ a = (a , a)

swap : ∀ {A B : U₀}
       → A × B → B × A
swap (a , b) = (b , a)

data Zero : U₀ where

data One : U₀ where 
  ∗ : One

id : ∀ {i} {A : U i} → A → A
id a = a

identity-on : (A : U₀) → A → A
identity-on A = (λ (x : A) → x)

infixr 70 _∘_
_∘_ : ∀ {i j k} {A : U i} {B : U j} {C : U k} → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g(f(x))

data Two : U₀ where
  ∗₁ : Two
  ∗₂ : Two


¬_ : U₀ → U₀
¬ A = A → Zero


