{-# OPTIONS --without-K #-}

module Formal-D-space where
  open import Basics
  open import FormalDisk
  open import FiberBundle
  open import InfinityGroups
  open import HomogeneousType
  open import Manifolds

  _is-a-formal_-space : (M : 𝒰₀) (D : 𝒰₀) → 𝒰₀
  M is-a-formal D -space = (𝔻 M) is-a D -fiber-bundle

  formal_-spaces : (D : 𝒰₀) → 𝒰₁
  formal D -spaces = ∑ (λ (M : 𝒰₀) → M is-a-formal D -space)

  underlying-type-of : {D : 𝒰₀} → formal D -spaces → 𝒰₀
  underlying-type-of (M , _) = M

  classifying-map-of-the-formal_-space_ :
      (D : 𝒰₀) (M : formal D -spaces)
    → (underlying-type-of M → BAut D)
  classifying-map-of-the-formal D -space (M , M-is-D-space) =
    let T∞-is-classified =
          logical-equivalences-between-the-four-definitions-of-fiber-bundles.def-to-def′
            (𝔻 M) M-is-D-space
    in _is-a′_-fiber-bundle′.χ T∞-is-classified

  the_-manifold_is-a-formal-𝔻ₑ-space :
      {V′ : 𝒰₀}
      (V : homogeneous-structure-on V′)
      (M : V -manifold)
      → let 𝔻ₑ = 𝔻 V′ (homogeneous-structure-on_.e V)
            M′ = _-manifold.M M
        in M′ is-a-formal 𝔻ₑ -space
  the V -manifold M is-a-formal-𝔻ₑ-space =
    the-formal-disk-bundle-on-a-manifold-is-a-fiber-bundle.𝔻M-is-a-fiber-bundle V M
