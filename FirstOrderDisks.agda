{-# OPTIONS --without-K #-}

module FirstOrderDisks where 
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Language
  open import Equivalences
  open import CommonEquivalences  
  open import Pullback
  open import PullbackSquare
  open import Im
  open import DependentTypes
  open import FormalDiskBundle



  -- we will now postulate first order infinitesimals
  -- they will be needed to define torsion-freeness
  -- of G-structures

  postulate
    first-order-disk-at_ : ∀ {M : U₀} → (x : M) → U₀

  D₁ = first-order-disk-at_

  -- inclusion of the disk in the space
  postulate
    ι-D₁ : ∀ {M : U₀} → (x : M)
           → D₁ x → M
    

  -- equivalence of formal-disks is stronger than first-order-disk-equivalence

  postulate
    equivalence-of-formal-disks-implies-equivalence-of-first-order-disks :
      ∀ {X Y : U₀} 
      → (x : X) → (y : Y)
      → formal-disk-at x ≃ formal-disk-at y → D₁ x ≃ D₁ y




