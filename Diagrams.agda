{-# OPTIONS --without-K #-}

module Diagrams where 
  open import Basics
  open import EqualityAndPaths
  open import Homotopies

  record Square {i} {A B C Z : U i} (f : A → C) (g : B → C) (z₁ : Z → A) (z₂ : Z → B) : U i where
    constructor the-square-commutes-by_
    field 
      homotopy : f ∘ z₁ ⇒ g ∘ z₂

  the-square-with-right_bottom_top_left_ :
    ∀ {i} {A B C Z : U i} 
    → (f : A → C) (g : B → C) (z₁ : Z → A) (z₂ : Z → B)
    → U i 
  the-square-with-right f bottom g top z₁ left z₂ = Square f g z₁ z₂


  -- record Triangle ?
