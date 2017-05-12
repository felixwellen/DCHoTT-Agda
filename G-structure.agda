{-# OPTIONS --without-K #-}

module G-structure where
  open import Basics
  open import EqualityAndPaths
  open import Equivalences
  open import Homotopies
  open import LeftInvertibleHspace
  open import FormalDiskBundle
  open import FiberBundle
  open import InfinityGroups
  open import PropositionalTruncation
  open import OneImage
  open import EtaleMaps
  open import Manifolds


  module G-structures-on-V-manifolds
    {V M W : U₀} (w : W ─ét→ M) (v : W ─ét→ V)
    (structure-on-V : left-invertible-structure-on V)
    (BG : U₀) (Bι : BG → BAut (formal-disk-at (left-invertible-structure-on_.e structure-on-V)))
    (M-is-a-manifold : M is-a-manifold-with-cover w
                      locally-like structure-on-V by v) where
    

    open left-invertible-structure-on_ structure-on-V
  
    De = formal-disk-at e

    χ : M → BAut De
    χ = the-formal-disk-bundle-on-a-manifold-is-a-fiber-bundle.classifying-morphism
        W M w structure-on-V v M-is-a-manifold

    {-
      Let BG be a delooping of a group G
      together with an 'inclusion' Bι : BG → BAut(D)
      into the Automorphisms of the formal disk 
      at the unit of V.
      A G-structure on a V-manifold M is given by a
      lift of the classifying morphism of T∞ V
      along Bι:
  
         ↗ BG 
        φ   |
       /   Bι
      /     ↓ 
      M ─→ BAut(D)
  
      We do not claim, that the type of those lifts
      is the correct moduli type of G-structures on M.
    -}

    G-structures : U₁
    G-structures = ∑ (λ (φ : M → BG) → Bι ∘ φ ⇒ χ)
    

  {-
      on a left invertible H-space V,
      there is always a 1-structure (for the trivial group 1)
  -}
  module trivial-structure-on-left-invertible-spaces
    {V : U₀} (structure-on-V : left-invertible-structure-on V) where

    open left-invertible-structure-on_ structure-on-V

    De = formal-disk-at e

    ψ : (x : V) → De ≃ (formal-disk-at x)
    ψ = triviality-of-the-formel-disk-bundle-the-nice-way.equivalences structure-on-V

    trivial-structure-on-V : U₁
    trivial-structure-on-V =
      G-structures-on-V-manifolds.G-structures
      id-as-étale-map id-as-étale-map
      structure-on-V
      One (λ x → (De , ∣ (x , refl) ∣ ))
      (left-invertible-H-spaces-are-manifolds structure-on-V)
