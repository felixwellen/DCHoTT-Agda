{-# OPTIONS --without-K #-}

module Formal-D-space where
  open import Basics
  open import EqualityAndPaths
  open import Equivalences
  open import Homotopies
  open import FormalDisk
  open import FormalDiskBundle
  open import FiberBundle
  open import HomogeneousType
  open import Manifolds

  _is-a-formal_-space : (M : 𝒰₀) (D : 𝒰₀) → 𝒰₀
  M is-a-formal D -space = (𝔻 M) is-a D -fiber-bundle

  formal_-spaces : (D : 𝒰₀) → 𝒰₁
  formal D -spaces = ∑ (λ (M : 𝒰₀) → M is-a-formal D -space)

  the_-manifold_is-a-formal-𝔻ₑ-space :
      {V′ : 𝒰₀}
      (V : homogeneous-structure-on V′)
      (M : V -manifold)
      → let 𝔻ₑ = 𝔻 V′ (homogeneous-structure-on_.e V)
            M′ = _-manifold.M M
        in M′ is-a-formal 𝔻ₑ -space
  the V -manifold M is-a-formal-𝔻ₑ-space =
    the-formal-disk-bundle-on-a-manifold-is-a-fiber-bundle.𝔻M-is-a-fiber-bundle V M
