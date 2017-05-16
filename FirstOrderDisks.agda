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
    specialize-to-first-order :
      ∀ {X Y : U₀} → (f : X → Y)
      → (x : X)
      → formal-disk-at x ≃ formal-disk-at (f x) → D₁ x ≃ D₁ (f x)




