{-# OPTIONS --without-K #-}


{-
  This is (among other things) part of an attempt to formalize Mike Shulman's
  real cohesion paper 
  (chapter 9, https://arxiv.org/abs/1509.07584 [1]).
  We do not work with the dedekind reals, but with a more
  abstract affine line object called '𝔸'
-}

module PostulateAffineLine where
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Equivalences
  open import HomogeneousType
  open import Flat renaming (_is-discrete to _is-crisply-discrete)
  open import Contractibility using (const)

  {-
    this auxilliary definition may find a better home some day...
  -}

  postulate
    𝔸 : 𝒰₀
    𝔸′ : homogeneous-structure-on 𝔸
    𝔸-nullfies-discrete-types :
      ∀ (A :{♭} 𝒰₀)
      → A is-crisply-discrete ≃ const {𝔸} {A} is-an-equivalence

  origin-of-𝔸 : 𝔸
  origin-of-𝔸 =
    let
      open homogeneous-structure-on_ 𝔸′
    in e
