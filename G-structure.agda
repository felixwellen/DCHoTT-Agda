{-# OPTIONS --without-K #-}

module G-structure where
  open import Basics
  open import Equivalences
  open import LeftInvertibleHspace
  open import FormalDiskBundle
  open import FiberBundle
  open import InfinityGroups
  open import Manifolds


  module G-structures-on-V-manifolds
    {V : U₀} (structure-on-V : left-invertible-structure-on V)
    (BG : U₀) (Bι : BG → BAut (formal-disk-at (structure-on-V))) where
    

    open left-invertible-structure-on_ structure-on-V
  
    De = formal-disk-at e

    χ : M → BAut De
    χ = triviality-of-the-formel-disk-bundle-the-nice-way.

    {-
      Let BG be a delooping of a group G
      together with an 'inclusion' Bι : BG → BAut(D)
      into the Automorphisms of the formal disk 
      at the unit of V.
      A G-structure on a V-manifold M is given by a
      lift of the classifying morphism of T∞ V
      along Bι:
  
        ↗  BG 
       /    |
      /     ↓ 
      M ─→ BAut(D)
  
      We do not claim, that the type of those lifts
      is the correct moduli type of G-structures on M.
    -}

    G-structures = ∑ (λ (φ : M → BG) → Bι ∘ φ ⇒  )
  
    module B1-structure-on-left-invertible-spaces where
  
      ψ : (x : V) → De ≃ (formal-disk-at x)
      ψ = triviality-of-the-formel-disk-bundle-the-nice-way.equivalences structure-on-V
