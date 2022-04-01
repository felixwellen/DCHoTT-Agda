{-# OPTIONS --without-K #-}

module formal-D-space where
  open import Basics
  open import EqualityAndPaths
  open import Equivalences
  open import Homotopies
  open import FormalDiskBundle
  open import FiberBundle

  _is-a-formal_-space : (M : 𝒰₀) (D : 𝒰₀) → 𝒰₀
  M is-a-formal D -space = T∞-as-dependent-type M is-a D -fiber-bundle

  formal_-spaces : (D : 𝒰₀) → 𝒰₁
  formal D -spaces = ∑ (λ (M : 𝒰₀) → M is-a-formal D -space)
