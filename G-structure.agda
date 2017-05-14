{-# OPTIONS --without-K #-}

module G-structure where
  open import Basics
  open import EqualityAndPaths
  open import Equivalences
  open import Homotopies
  open import Univalence
  open import LeftInvertibleHspace
  open import FormalDiskBundle
  open import FiberBundle
  open import InfinityGroups
  open import PropositionalTruncation
  open import OneImage
  open import EtaleMaps
  open import Manifolds

  record group-over-structure-group-of_ {V : U₀}
    (structure-on-V : left-invertible-structure-on V) : U₁ where
    constructor group-given-by-delooping_with-unit_and-morphism_
    field
      BG : U₀
      Be : BG
      Bφ : BG → BAut (formal-disk-at (left-invertible-structure-on_.e structure-on-V))


  module G-structures-on-V-manifolds
    {V M W : U₀} (w : W ─ét→ M) (v : W ─ét→ V)
    (structure-on-V : left-invertible-structure-on V)
    (reduction : group-over-structure-group-of structure-on-V)
    (M-is-a-manifold : M is-a-manifold-with-cover w
                      locally-like structure-on-V by v) where
    

    open left-invertible-structure-on_ structure-on-V
    open group-over-structure-group-of_ reduction

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
    G-structures = ∑ (λ (φ : M → BG) → Bφ ∘ φ ⇒ χ)
    

  {-
      on a left invertible H-space V,
      there is always a 1-structure (for the trivial group 1)
  -}
  module trivial-structure-on-left-invertible-spaces
    {V : U₀}
    (structure-on-V : left-invertible-structure-on V) 
    (group-over-BAutD : group-over-structure-group-of structure-on-V)
    where

    open left-invertible-structure-on_ structure-on-V

    De = formal-disk-at e

    G-structures-on-V : U₁
    G-structures-on-V =
      G-structures-on-V-manifolds.G-structures
      id-as-étale-map id-as-étale-map
      structure-on-V
      group-over-BAutD
      (left-invertible-H-spaces-are-manifolds structure-on-V)

    ψ : (x : V) → De ≃ (formal-disk-at x)
    ψ = triviality-of-the-formel-disk-bundle-the-nice-way.equivalences structure-on-V

    open group-over-structure-group-of_ group-over-BAutD

    -- calculate the classifying morphism for V
    -- i.e. give an explicit description
    χ-V : V → BAut De
    χ-V x = ((formal-disk-at x) , ∣ (∗ , univalence (ψ x)) ∣)

    V-is-a-manifold = (left-invertible-H-spaces-are-manifolds structure-on-V)

    χ′ = G-structures-on-V-manifolds.χ id-as-étale-map id-as-étale-map
              structure-on-V group-over-BAutD
              V-is-a-manifold
    χ-V-is-the-classifying-morphism :
      χ-V ⇒ χ′
    χ-V-is-the-classifying-morphism = 1-monos-are-monos χ-V χ′ (ι-BAut De) (ι-im₁-is-1-mono (λ ∗₃ → De))
      (λ (x : V) →
           the-formal-disk-bundle-on-a-manifold-is-a-fiber-bundle.commutes-with-the-dependent-replacement-of-T∞
           V V id-as-étale-map structure-on-V id-as-étale-map V-is-a-manifold
           x)
{-    
    trivialization-structure : G-structures-on-V
    trivialization-structure =
      ((λ x → Be) , (λ x →
        {! Bφ(Be)
        ≈⟨ ? ⟩
          
        ≈∎!}))

    trivial_-structure-on-V :
      ∀ (reduction : group-over-structure-group-of structure-on-V)
      → {!!}
    trivial_-structure-on-V = {!!}
-}

  {-
    We will now work towards the definition of 
    torision-free G-structures.
    For this, we need to be able to compare
    G-structures on first-order-disks
  -}

  
