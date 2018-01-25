{-# OPTIONS --without-K #-}

module Manifolds where 
  open import Basics 
  open import EqualityAndPaths
  open import PropositionalTruncation
  open import DependentTypes
  open import Fiber
  open import Equivalences renaming (underlying-map-of to underlying-map-of-the-equivalence)
  open import Pullback
  open import PullbackSquare
  open import InfinityGroups
  open import Contractibility
  open import Homotopies
  open import Im
  open import FormalDiskBundle
  open import EtaleMaps
  open import Language
  open import OneImage
  open import FiberBundle
  open import FormalDisk
  open import HomogeneousType
  open import PropertiesOfEtaleMaps

  _is-a-manifold-with-cover_locally-like_by_ : 
    ∀ {W : U₀} {V : U₀} (M : U₀)
    → (w : W ─ét→ M) → (structure-on-V : homogeneous-structure-on V) → (v : W ─ét→ V)
    → U₀
  M is-a-manifold-with-cover w locally-like structure-on-V by v =
    underlying-map-of w is-1-epi

  homogeneous-spaces-are-manifolds :
    ∀ {V : U₀} (structure-on-V : homogeneous-structure-on V)
    → V is-a-manifold-with-cover id-as-étale-map locally-like structure-on-V by id-as-étale-map
  homogeneous-spaces-are-manifolds _ = equivalences-are-1-epi id-as-equivalence
  

  module the-formal-disk-bundle-on-a-manifold-is-a-fiber-bundle 
         {V : 𝒰} (U M : 𝒰) (w : U ─ét→ M) 
         (structure-on-V : homogeneous-structure-on V) (v : U ─ét→ V)
         (M-is-a-manifold : M is-a-manifold-with-cover w
                            locally-like structure-on-V by v) where

         open homogeneous-structure-on_ structure-on-V
         𝔻ₑ = 𝔻 V e -- formal-disk-at e


         trivialization-of-𝔻U : (x : U) → 𝔻 U x ≃ 𝔻ₑ
         trivialization-of-𝔻U x =
           let
             open formal-disk-bundles-are-preserved-by-étale-base-change v
             open triviality-of-the-formal-disk-bundle-over-homogeneous-types structure-on-V
           in  identifications-of-all-formal-disks (v $ét x) ⁻¹≃
             ∘≃
               conclusion-as-equivalence-above-the-map x

         w′ : U ↠ M
         w′ = (underlying-map-of w) is-1-epi-by M-is-a-manifold

         𝔻M-is-a-fiber-bundle″ : (𝔻 M) is-a″ 𝔻ₑ -fiber-bundle″
         𝔻M-is-a-fiber-bundle″ =
           let
             open formal-disk-bundles-are-preserved-by-étale-base-change w
           in record
             {
               V = U ;
               v = w′ ;
               pullback-trivializes = λ x →
                 trivialization-of-𝔻U x ∘≃ conclusion-as-equivalence-above-the-map x ⁻¹≃
             }

         open logical-equivalences-between-the-four-definitions-of-fiber-bundles {B = M} {F = 𝔻ₑ}

         𝔻M-is-a-fiber-bundle : (𝔻 M) is-a 𝔻ₑ -fiber-bundle
         𝔻M-is-a-fiber-bundle = def″-to-def (𝔻 M) 𝔻M-is-a-fiber-bundle″
            
         𝔻M-is-a-fiber-bundle⁗ : (∑π₁-from (𝔻 M)) is-a⁗ 𝔻ₑ -fiber-bundle⁗
         𝔻M-is-a-fiber-bundle⁗ = def-to-def⁗ (𝔻 M) 𝔻M-is-a-fiber-bundle
         
         classifying-morphism : M → BAut 𝔻ₑ
         classifying-morphism =
           let
             open _is-a⁗_-fiber-bundle⁗ 𝔻M-is-a-fiber-bundle⁗
           in χ

         classifying-morphism-is-natural :
           ι-BAut 𝔻ₑ ∘ classifying-morphism ⇒ (𝔻 M)
         classifying-morphism-is-natural x = refl
         
         all-formal-disks-are-merely-equivalent :
           ∀ (x : M)
           → ∥ formal-disk-at x ≃ 𝔻ₑ ∥
         all-formal-disks-are-merely-equivalent =
           let
             open _is-a_-fiber-bundle 𝔻M-is-a-fiber-bundle
           in all-fibers-are-merely-equivalent 

         commutes-with-the-dependent-replacement-of-T∞′′ :
           (λ (x : M) → 𝔻 _ x) ⇒ (ι-BAut 𝔻ₑ) ∘ classifying-morphism
         commutes-with-the-dependent-replacement-of-T∞′′ x = refl

         {-

         T∞ U is a trivial bundle, which is witnessed by the square
         
         T∞U ───→ 𝔻ₑ
          | ⌟     |
          |       |
          ↓       ↓
          U ────→ 1

         constructed below

         -}

         T∞U-is-trivial : 
           pullback-square-with-right (λ (d : 𝔻ₑ) → ∗)
             bottom (λ (x : U) → ∗)
             top _
             left (p-of-T∞ U)
         T∞U-is-trivial =
           pasting-of-pullback-squares 
             (formal-disk-bundles-are-preserved-by-étale-base-change.conclusion v)  
             (triviality-of-the-formal-disk-bundle-over-homogeneous-types.as-product-square
               structure-on-V)

         {-

            T∞U─id─→T∞U 
             | ⌟     |   
             p       p   and ? 
             |       |
             ↓       ↓
             U ─id─→ U

         -}

         T∞U-is-equivalent-to-w*T∞M :
           pullback-square-with-right (p-of-T∞ U)
             bottom id
             top _
             left _
         T∞U-is-equivalent-to-w*T∞M =
           (formal-disk-bundles-are-preserved-by-étale-base-change.conclusion w)
           and (complete-to-pullback-square (p-of-T∞ M) (underlying-map-of w))
           pull-back-the-same-cospan-so-the-first-may-be-replaced-by-the-second-in-the-square
           (pullback-square-from-identity-of-morphisms (p-of-T∞ U))

         w*T∞M-is-trivial :
           pullback-square-with-right (λ (d : 𝔻ₑ) → ∗)
             bottom (λ (x : U) → ∗)
             top _
             left ((underlying-map-of w) *→ (p-of-T∞ M))
         w*T∞M-is-trivial =
           substitute-homotopic-left-map
             (pasting-of-pullback-squares
               T∞U-is-equivalent-to-w*T∞M
               T∞U-is-trivial)
             ((underlying-map-of w) *→ (p-of-T∞ M))
             (deduced-equivalence-factors-the-left-map
                (complete-to-pullback-square (p-of-T∞ M) (underlying-map-of w))
                (formal-disk-bundles-are-preserved-by-étale-base-change.conclusion
                 w)
                ⁻¹⇒)

         T∞M-is-a-fiber-bundle : (p-of-T∞ M) is-a′ 𝔻ₑ -fiber-bundle′
         T∞M-is-a-fiber-bundle =
           let
             v́-as-surjection = (underlying-map-of w) is-1-epi-by M-is-a-manifold
           in
             on U the-pullback-along v́-as-surjection
             is-trivial-by top-map-of w*T∞M-is-trivial
             and w*T∞M-is-trivial

         classifying-morphism′ : M → BAut 𝔻ₑ
         classifying-morphism′ =
           all-fiber-bundle-are-associated.classifying-morphism (p-of-T∞ M) T∞M-is-a-fiber-bundle
{-
         commutes-with-the-dependent-replacement-of-T∞′ :
           (dependent-replacement (p-of-T∞ M)) ⇒ (ι-BAut 𝔻ₑ) ∘ classifying-morphism 
         commutes-with-the-dependent-replacement-of-T∞′ x =
           all-fiber-bundle-are-associated.as-U₀-morphism (p-of-T∞ M)
             T∞M-is-a-fiber-bundle x

         -- the following makes a probably unnecessary use of univalence
         open import Univalence
         commutes-with-the-dependent-replacement-of-T∞ :
           (λ (x : M) → 𝔻 _ x) ⇒ (ι-BAut 𝔻ₑ) ∘ classifying-morphism
         commutes-with-the-dependent-replacement-of-T∞ x =
             𝔻 _ x
           ≈⟨ univalence
                (pullback-definition-and-dependent-version-agree.on-fibers M x ⁻¹≃) ⟩
             (dependent-replacement (p-of-T∞ M)) x
            ≈⟨ commutes-with-the-dependent-replacement-of-T∞′ x ⟩
             ((ι-BAut 𝔻ₑ) ∘ classifying-morphism) x
           ≈∎
-}
