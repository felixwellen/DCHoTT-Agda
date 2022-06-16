{-# OPTIONS --without-K #-}

module Manifolds where
  open import Basics
  open import EqualityAndPaths
  open import PropositionalTruncation
  open import DependentTypes
  open import Fiber
  open import Equivalences renaming (underlying-map-of to underlying-map-of-the-equivalence)
  open import InfinityGroups
  open import Contractibility
  open import Homotopies
  open import Im
  open import FormalDiskBundle
  open import FormallyEtaleMaps
  open import Language
  open import Image
  open import FiberBundle
  open import FormalDisk
  open import HomogeneousType
  open import ImHomogeneousType
  open import PropertiesOfEtaleMaps


  record _-manifold {V′ : 𝒰₀} (V : homogeneous-structure-on V′) : 𝒰₁ where
    field
      M : 𝒰₀
      W : 𝒰₀
      w : W ─ét→ M
      w-covers : (w ét→) is-surjective
      v : W ─ét→ V′

    cover-as-surjection : W ↠ M
    cover-as-surjection = (w ét→) is-surjective-by w-covers


  homogeneous-space-as-manifold :
    ∀ {V : 𝒰₀} (V′ : homogeneous-structure-on V)
    → V′ -manifold   -- V is-a-manifold-with-cover id-as-étale-map locally-like structure-on-V by id-as-étale-map
  homogeneous-space-as-manifold _ =
    record
      {
        w = id-as-étale-map ;
        w-covers = λ b → ∣ b is-in-the-fiber-by refl ∣ ;
        v = id-as-étale-map
      }

  module the-formal-disk-bundle-on-a-manifold-is-a-fiber-bundle
         {V′ : 𝒰₀}
         (V : homogeneous-structure-on V′)
         (M′ : V -manifold)
         where

         open homogeneous-structure-on_ V
         𝔻ₑ = 𝔻 V′ e

         open _-manifold M′

         trivialization-of-𝔻U : (x : W) → 𝔻 W x ≃ 𝔻ₑ
         trivialization-of-𝔻U x =
           let
             open formal-disk-bundles-are-preserved-by-étale-base-change v
             open triviality-of-the-formal-disk-bundle-over-homogeneous-types V
           in  identifications-of-all-formal-disks (v $ét x) ⁻¹≃
             ∘≃
               conclusion-as-equivalence-above-the-map x

         w′ : W ↠ M
         w′ = cover-as-surjection

         𝔻M-is-a-fiber-bundle″ : (𝔻 M) is-a″ 𝔻ₑ -fiber-bundle″
         𝔻M-is-a-fiber-bundle″ =
           let
             open formal-disk-bundles-are-preserved-by-étale-base-change w
           in record
             {
               V = W ;
               v = w′ ;
               pullback-trivializes = λ x →
                 trivialization-of-𝔻U x ∘≃ conclusion-as-equivalence-above-the-map x ⁻¹≃
             }

         open logical-equivalences-between-the-four-definitions-of-fiber-bundles {B = M} {F = 𝔻ₑ}

         𝔻M-is-a-fiber-bundle : (𝔻 M) is-a 𝔻ₑ -fiber-bundle
         𝔻M-is-a-fiber-bundle = def″-to-def (𝔻 M) 𝔻M-is-a-fiber-bundle″

         𝔻M-is-a-fiber-bundle⁗ : (∑π₁-from (𝔻 M)) is-a′ 𝔻ₑ -fiber-bundle′
         𝔻M-is-a-fiber-bundle⁗ = def-to-def′ (𝔻 M) 𝔻M-is-a-fiber-bundle

         classifying-morphism : M → BAut 𝔻ₑ
         classifying-morphism = classifying-morphism′ 𝔻M-is-a-fiber-bundle⁗

         classifying-morphism-is-natural :
           ι-BAut 𝔻ₑ ∘ classifying-morphism ⇒ (𝔻 M)
         classifying-morphism-is-natural = compute-classifying-morphism 𝔻M-is-a-fiber-bundle

         all-formal-disks-are-merely-equivalent :
           ∀ (x : M)
           → ∥ formal-disk-at x ≃ 𝔻ₑ ∥
         all-formal-disks-are-merely-equivalent =
           let
             open _is-a_-fiber-bundle 𝔻M-is-a-fiber-bundle
           in all-fibers-are-merely-equivalent

         commutes-with-the-dependent-replacement-of-T∞′′ :
           𝔻 M ⇒ (ι-BAut 𝔻ₑ) ∘ classifying-morphism
         commutes-with-the-dependent-replacement-of-T∞′′ x = classifying-morphism-is-natural x ⁻¹
