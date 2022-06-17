{-# OPTIONS --without-K #-}

module G-structure where
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Univalence
  open import FormalDiskBundle
  open import FiberBundle
  open import InfinityGroups
  open import FormallyEtaleMaps
  open import PropertiesOfEtaleMaps
  open import Manifolds
  open import FormalDisk
  open import HomogeneousType
  open import Formal-D-space

  record groups-over-automorphismgroup-of_ (D : 𝒰₀) : 𝒰₁ where
    field
      BG : 𝒰₀
      Be : BG
      Bι : BG → BAut D
      path-between-units : Bι(Be) ≈ e-BAut D

  -- shorthand
  χ𝔻 : {D : 𝒰₀}
       → (M : formal D -space) → (∑π₁ M) → BAut D
  χ𝔻 (M , M-is-D-space) = classifying-map-of-the-formal _ -space (M , M-is-D-space)

  module _
    {D : 𝒰₀}
    (M : formal D -space)
    (group-over-BAutD : groups-over-automorphismgroup-of D)
    where
    open groups-over-automorphismgroup-of_ group-over-BAutD
    {-
      Let BG be a delooping of a group G
      together with a pointed map Bι : BG → BAut(D)
      into the Automorphisms of the model formal disk in M.
      A G-structure on a V-manifold M is given by a
      lift of the witness χ : M → BAut(D),
      that M is a formal D-space,
      along Bι:

         ↗ BG
        ϕ   |
       /   Bι
      /     ↓
      M ─→ BAut(D)

    -}

    G-structures : U₁
    G-structures = ∑ (λ (ϕ : ∑π₁ M → BG) → Bι ∘ ϕ ⇒ χ𝔻 M)

  module _
      {D : 𝒰₀}
      (M : formal D -space)
      (N : formal D -space)
      (f : (∑π₁ M) ─ét→ (∑π₁ N))
    where

    private
      f' = Σπ₁ f

      𝔻-homotopy : 𝔻 (∑π₁ N) ∘ f' ⇒ 𝔻 (∑π₁ M)
      𝔻-homotopy x = univalence (d⁻¹≃ f x)

    χ𝔻→ : χ𝔻 N ∘ f' ⇒ χ𝔻 M
    χ𝔻→ x =
      prove-equality-of-classifying-maps
         (χ𝔻 N ∘ f') (χ𝔻 M)
         (λ x → ι-BAut D ((χ𝔻 N ∘ f') x) ≈⟨ compute-classifying-morphism
                                             (∑π₂ N) (f' x) ⟩
                (𝔻 (∑π₁ N) ∘ f') x       ≈⟨ 𝔻-homotopy x ⟩
                (𝔻 (∑π₁ M)) x            ≈⟨ compute-classifying-morphism
                                             (∑π₂ M) x ⁻¹ ⟩
                ι-BAut D (χ𝔻 M x) ≈∎)
         x
      where open logical-equivalences-between-the-four-definitions-of-fiber-bundles


  module _
      {D : 𝒰₀}
      (M : formal D -space)
      (N : formal D -space)
      (f : (∑π₁ M) ─ét→ (∑π₁ N))
      (G : groups-over-automorphismgroup-of D)
    where
    open groups-over-automorphismgroup-of_ G
    private
      G-str-M = G-structures M G
      G-str-N = G-structures N G

    G-str→ : G-str-N → G-str-M
    G-str→ (χ , η) =
      χ ∘ (∑π₁ f) ,
      λ x → η (∑π₁ f x) • χ𝔻→ M N f x

  module trivial-structure-on-homogeneous-types
    {V′ : 𝒰₀}
    (V : homogeneous-structure-on V′)
    (group-over-BAut𝔻ₑ : groups-over-automorphismgroup-of (formal-disk-of V))
    where

    open homogeneous-structure-on_ V

    𝔻ₑ = formal-disk-at e

    V-is-a-𝔻ₑ-space = the V -manifold (homogeneous-space-as-manifold V) is-a-formal-𝔻ₑ-space

    G-structures-on-V : 𝒰₁
    G-structures-on-V =
      G-structures
      (_ , V-is-a-𝔻ₑ-space)
      group-over-BAut𝔻ₑ

    φ : (x : V′) → 𝔻ₑ ≃ 𝔻 _ x
    φ = triviality-of-the-formal-disk-bundle-over-homogeneous-types.identifications-of-all-formal-disks V

    φ-as-homotopy : (λ _ → 𝔻ₑ) ⇒ 𝔻 V′
    φ-as-homotopy x = univalence (φ x)

    open groups-over-automorphismgroup-of_ group-over-BAut𝔻ₑ

    χ′ : V′ → BAut 𝔻ₑ
    χ′ = χ𝔻 (_ , V-is-a-𝔻ₑ-space)

    trivial-structure : G-structures-on-V
    trivial-structure =
      (λ _ → Be) ,
      λ (x : V′) →
        Bι Be         ≈⟨ path-between-units ⟩
        e-BAut 𝔻ₑ     ≈⟨ prove-equality-of-classifying-maps
                         (λ (x : V′) → e-BAut 𝔻ₑ) χ′ φ-as-homotopy′ x ⟩
        χ′ x          ≈∎
      where open logical-equivalences-between-the-four-definitions-of-fiber-bundles
            φ-as-homotopy′ : (λ _ → 𝔻ₑ) ⇒ (ι-BAut 𝔻ₑ ∘ χ′)
            φ-as-homotopy′ x =
              𝔻ₑ                      ≈⟨  φ-as-homotopy x ⟩
              𝔻 V′ x                 ≈⟨ compute-classifying-morphism
                                        (formal
                                          𝔻ₑ -spaces-are-fiber-bundles V-is-a-𝔻ₑ-space)
                                         x ⁻¹ ⟩
              (ι-BAut 𝔻ₑ ∘ χ′) x     ≈∎

    {-
      We will now work towards the definition of
      torision-free G-structures.
      For this, we need to be able to compare
      G-structures on formal disks
    -}
    ι-𝔻ₑ : 𝔻ₑ → V′
    ι-𝔻ₑ = inclusion-of-formal-disk-at e

    trivial-structure-restricted-to-𝔻ₑ :
      𝔻ₑ → BG
    trivial-structure-restricted-to-𝔻ₑ =
      let
        ψ : V′ → BG
        ψ = (∑π₁ trivial-structure)
      in ψ ∘ ι-𝔻ₑ


{-
  module G-str-functorial𝔻-homotopy
      {D : 𝒰₀}
      (M N O : formal D -space)
      (G : groups-over-automorphismgroup-of D)
      (f : (∑π₁ M) ─ét→ (∑π₁ N))
      (g : (∑π₁ N) ─ét→ (∑π₁ O))
    where
    private
      f' = ∑π₁ f
      g' = ∑π₁ g

    G-str-f   = G-str→   M N f G
    G-str-g   = G-str→   N O g G
    G-str-g∘f = G-str→ M O (g ∘ét f) G

    →∘-comm : G-str-g∘f ⇒ G-str-f ∘ G-str-g
    →∘-comm (ϕ , η) =
      construct-path-in-∑
        (ϕ ∘ g' ∘ f') (ϕ ∘ g' ∘ f')
        (∑π₂ (G-str-g∘f (ϕ , η))) (∑π₂ (G-str-f (G-str-g (ϕ , η))))
        refl
        eq
      where
        eq : ∑π₂ (G-str-g∘f (ϕ , η)) ≈ ∑π₂ (G-str-f (G-str-g (ϕ , η)))
        eq =
          fun-ext
            λ (x : (∑π₁ M))
             → {!!}

-}
