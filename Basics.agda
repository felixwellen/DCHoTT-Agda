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


{- 
  
  supposed to be standard names in the future:
  (one advantage is, that coverings may be called 'U'...)
-}
𝒰 = U₀   
𝒰₀ = U₀
𝒰₁ = U₁

𝒰- = U

domain : ∀ {A B : 𝒰} → (A → B) → 𝒰
domain {A} {_} _ = A

codomain : ∀ {A B : 𝒰} → (A → B) → 𝒰
codomain {_} {B} _ = B


data Bool : 𝒰 where
  true : Bool
  false : Bool


Π : ∀ {i j} → {A : 𝒰- i} → (P : A → 𝒰- j) → 𝒰- (i ⊔ j)
Π {_} {_} {A} P = (a : A) → P a

π-Π : ∀ {A : 𝒰} {P : A → 𝒰}
      → (a : A) → Π P → P a
π-Π a = λ s → s a      

infix 20 _,_
record ∑ {i j} {A : 𝒰- i} (P : A → 𝒰- j) : 𝒰- (i ⊔ j) where
  constructor _,_
  field
    a : A
    p : P a

ι-∑ : ∀ {i} {j} {A : 𝒰- i} {P : A → 𝒰- j}
      → (a : A) → P a → ∑ P
ι-∑ a p = (a , p)


∑π₁ : ∀ {i} {j} {A : 𝒰- i} {P : A → 𝒰- j} 
  → ∑ P → A
∑π₁ (a , _) = a

∑π₁-from_ :
  ∀ {i} {j} {A : 𝒰- i} (P : A → 𝒰- j)
  → ∑ P → A
∑π₁-from P = ∑π₁

∑π₂ : ∀ {i} {j} {A : 𝒰- i} {P : A → 𝒰- j}
  → (x : ∑ P) → P (∑π₁ x)
∑π₂ (a , p) = p  

∑π₂-from_ :
  ∀ {i} {j} {A : 𝒰- i} (P : A → 𝒰- j)
  → (x : ∑ P) → P (∑π₁ x)
∑π₂-from P = ∑π₂

Π-to-∑ : ∀ {A : 𝒰} {P : A → 𝒰}
         → Π P → A → ∑ P
Π-to-∑ s a = (a , s a)

infix 60 _×_

_×_ : 
  ∀ {i j} 
  → (A : 𝒰- i) → (B : 𝒰- j) → 𝒰- (i ⊔ j)
A × B = ∑ (λ (a : A) → B)

_×→_ : ∀ {A B A′ B′ : 𝒰} → (A → B) → (A′ → B′) → (A × A′ → B × B′)
f ×→ g = λ { (a , b) → f a , g b }

_,→_ : ∀ {X A B : 𝒰} → (X → A) → (X → B) → (X → A × B)
f ,→ g = λ x → (f x , g x)

π₁ : ∀ {i} {A : 𝒰- i} {B : 𝒰- i} → A × B → A
π₁ (a , b) = a

π₂ : ∀ {i} {A : 𝒰- i} {B : 𝒰- i} → A × B → B
π₂ (a , b) = b 


π₁-from_×_ : ∀ {i} (A : 𝒰- i) (B : 𝒰- i) → A × B → A
π₁-from A × B = π₁

π₂-from_×_ : ∀ {i} (A : 𝒰- i) (B : 𝒰- i) → A × B → B
π₂-from A × B = π₂

Δ : ∀ {A : 𝒰}
    → A → A × A
Δ a = (a , a)

swap : ∀ {A B : 𝒰}
       → A × B → B × A
swap (a , b) = (b , a)

data Zero : 𝒰 where

data One : 𝒰 where 
  ∗ : One

id : ∀ {i} {A : 𝒰- i} → A → A
id a = a

identity-on : (A : 𝒰) → A → A
identity-on A = (λ (x : A) → x)

infixr 70 _∘_
_∘_ : ∀ {i j k} {A : 𝒰- i} {B : 𝒰- j} {C : 𝒰- k} → (B → C) → (A → B) → (A → C)
g ∘ f = λ x → g(f(x))

data Two : 𝒰 where
  ∗₁ : Two
  ∗₂ : Two


¬_ : 𝒰 → 𝒰
¬ A = A → Zero


