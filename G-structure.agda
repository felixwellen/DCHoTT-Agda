{-# OPTIONS --without-K #-}

module G-structure where
  open import Basics
  open import EqualityAndPaths
  open import Equivalences renaming (underlying-map-of to as-plain-map)
  open import Homotopies
  open import Univalence
  open import FormalDiskBundle
  open import FiberBundle
  open import InfinityGroups
  open import PropositionalTruncation
  open import Image
  open import EtaleMaps
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

  module G-structures-on-𝔻ₑ-spaces
    {D : 𝒰₀} (M : 𝒰₀)
    (M-is-D-space : M is-a-formal D -space)
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

    χ : M → BAut D
    χ = classifying-map-of-the-formal D -space (M , M-is-D-space)

    G-structures : U₁
    G-structures = ∑ (λ (ϕ : M → BG) → Bι ∘ ϕ ⇒ χ)


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
      G-structures-on-𝔻ₑ-spaces.G-structures
      V′
      V-is-a-𝔻ₑ-space
      group-over-BAut𝔻ₑ

    φ : (x : V′) → 𝔻ₑ ≃ 𝔻 _ x
    φ = triviality-of-the-formal-disk-bundle-over-homogeneous-types.identifications-of-all-formal-disks V

    φ-as-homotopy : (λ _ → 𝔻ₑ) ⇒ 𝔻 V′
    φ-as-homotopy x = univalence (φ x)

    open groups-over-automorphismgroup-of_ group-over-BAut𝔻ₑ

    χ′ : V′ → BAut 𝔻ₑ
    χ′ = G-structures-on-𝔻ₑ-spaces.χ V′ V-is-a-𝔻ₑ-space group-over-BAut𝔻ₑ

    trivial-structure : G-structures-on-V
    trivial-structure =
      (λ _ → Be) ,
      λ (x : V′) →
        Bι Be         ≈⟨ path-between-units ⟩
        e-BAut 𝔻ₑ     ≈⟨ injectives-are-monos
                           (λ (x : V′) → e-BAut 𝔻ₑ) χ′
                           (ι-BAut 𝔻ₑ) (ι-im₁-is-injective (λ ∗₃ → 𝔻ₑ)) φ-as-homotopy′ x ⟩
        χ′ x          ≈∎
      where open logical-equivalences-between-the-four-definitions-of-fiber-bundles
            φ-as-homotopy′ : (λ _ → 𝔻ₑ) ⇒ (ι-BAut 𝔻ₑ ∘ χ′)
            φ-as-homotopy′ x = 𝔻ₑ                      ≈⟨  φ-as-homotopy x ⟩
                               𝔻 V′ x                 ≈⟨ compute-classifying-morphism
                                                          (formal 𝔻ₑ -spaces-are-fiber-bundles V-is-a-𝔻ₑ-space) x ⁻¹ ⟩
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
  record groups-over-structure-group-of_ {V : 𝒰₀}
    (structure-on-V : homogeneous-structure-on V) : 𝒰₁ where
    field
      BG : 𝒰₀
      Be : BG
      Bφ : BG → BAut (formal-disk-of structure-on-V)
      path-between-units : Bφ(Be) ≈ e-BAut (formal-disk-of structure-on-V)

  module G-structures-on-V-manifolds
    {V′ : 𝒰₀} -- (w : U ─ét→ M) (v : U ─ét→ V′)
    (V : homogeneous-structure-on V′)
    (reduction : groups-over-structure-group-of V)
    (M′ : V -manifold) where


    open homogeneous-structure-on_ V
    open groups-over-structure-group-of_ reduction
    open _-manifold M′

    𝔻ₑ = formal-disk-at e

    χ : M → BAut 𝔻ₑ
    χ = the-formal-disk-bundle-on-a-manifold-is-a-fiber-bundle.classifying-morphism V M′

    {-
      Let BG be a delooping of a group G
      together with a pointed map Bι : BG → BAut(𝔻ₑ)
      into the Automorphisms of the formal disk
      at the unit of V.
      A G-structure on a V-manifold M is given by a
      lift of the classifying morphism of T∞ V
      along Bι:

         ↗ BG
        φ   |
       /   Bφ
      /     ↓
      M ─→ BAut(𝔻ₑ)

      We do not claim, that the type of those lifts
      is the correct moduli type of G-structures on M.
    -}

    G-structures : U₁
    G-structures = ∑ (λ (φ : M → BG) → Bφ ∘ φ ⇒ χ)

  {-
      on a left invertible H-space V,
      there is always a 1-structure (for the trivial group 1)
      and by composing, a G-structure
  -}
  module trivial-structure-on-homogeneous-types
    {V′ : 𝒰₀}
    (V : homogeneous-structure-on V′)
    (group-over-BAut𝔻ₑ : groups-over-structure-group-of V)
    where

    open homogeneous-structure-on_ V

    𝔻ₑ = formal-disk-at e

    G-structures-on-V : 𝒰₁
    G-structures-on-V =
      G-structures-on-V-manifolds.G-structures
      V
      group-over-BAut𝔻ₑ
      (homogeneous-space-as-manifold V)

    φ : (x : V′) → 𝔻ₑ ≃ 𝔻 _ x
    φ = triviality-of-the-formal-disk-bundle-over-homogeneous-types.identifications-of-all-formal-disks V

    φ-as-homotopy : (λ _ → 𝔻ₑ) ⇒ 𝔻 V′
    φ-as-homotopy x = univalence (φ x)


    open groups-over-structure-group-of_ group-over-BAut𝔻ₑ


    χ′ = G-structures-on-V-manifolds.χ
              V group-over-BAut𝔻ₑ
              (homogeneous-space-as-manifold V)

    trivial-structure : G-structures-on-V
    trivial-structure =
      ((λ _ → Be) ,
        (λ (x : V′) → path-between-units • injectives-are-monos (λ (x : V′) → e-BAut 𝔻ₑ) χ′ (ι-BAut 𝔻ₑ)
             (ι-im₁-is-injective (λ ∗₃ → 𝔻ₑ)) φ-as-homotopy x))

  {-
    We will now work towards the definition of
    torision-free G-structures.
    For this, we need to be able to compare
    G-structures on formal disks
  -}
    𝔻-at = formal-disk-at_
    ι-𝔻ₑ = inclusion-of-formal-disk-at e

    trivial-structure-restricted-to-𝔻ₑ :
      formal-disk-at e → BG
    trivial-structure-restricted-to-𝔻ₑ =
      let
        ψ : V′ → BG
        ψ = (∑π₁ trivial-structure)
      in ψ ∘ ι-𝔻ₑ

------------ continue here -------------------------


    {-
      now, for a general V-manifold
    -}
    module torsion-free-structures
      (M′ : V -manifold)
                 where

      open _-manifold M′

      ∗𝔻 : (x₀ : M) → formal-disk-at x₀
      ∗𝔻 x₀ = (x₀ , refl)

      χ-M : M → BAut 𝔻ₑ
      χ-M =
        the-formal-disk-bundle-on-a-manifold-is-a-fiber-bundle.classifying-morphism V M′

      all-𝔻s-are-merely-equivalent :
        ∀ (x : M)
        → ∥  𝔻-at x ≃ 𝔻ₑ ∥
      all-𝔻s-are-merely-equivalent x =
        the-formal-disk-bundle-on-a-manifold-is-a-fiber-bundle.all-formal-disks-are-merely-equivalent V M′ x

      G-structures-on-M =
        G-structures-on-V-manifolds.G-structures
         V group-over-BAut𝔻ₑ M′

      _is-torsion-free :
        G-structures-on-M → 𝒰₁
      (lift-of-g , homotopy) is-torsion-free =
        {-
          to decide if a G-structure is torsion free,
          we have to compare it locally to the trivial G-structure.
          This means comparing all triangles obtained by restricting the
          G-Structure to the formal disk at some point x


                ↗ BG                       ↗ BG
               /   |                      φ   |
              /   Bφ         ≈           /   Bφ
             /     ↓                    /     ↓
          𝔻ₓ ──→ BAut(𝔻ₑ)      𝔻ₓ ──→ M ──→ BAut(𝔻ₑ)

          to the 𝔻ₑ-triangle of the trivial G-Structure

                ↗ BG
              B1   |
              /   Bφ
             /     ↓
          𝔻ₑ ──→ BAut(𝔻ₑ)

        -}
        let
          -- classifying map of T∞V
          ξ = G-structures-on-V-manifolds.χ
              V group-over-BAut𝔻ₑ
              (homogeneous-space-as-manifold V)

          -- the triangle type discussed above
          triangles-at : BAut 𝔻ₑ → 𝒰₁
          triangles-at = λ {(Dx , _) → ∑ λ (f : Dx →  BG)
                                     → ∑ λ (g : Dx →  BAut 𝔻ₑ)
                                           → Bφ ∘ f ⇒ g}

          triangle-of-the-trivial-G-structure :
            triangles-at (e-BAut 𝔻ₑ)
          triangle-of-the-trivial-G-structure =
            (trivial-structure-restricted-to-𝔻ₑ ,
              (ξ ∘ ι-𝔻ₑ  , (pre-whisker ι-𝔻ₑ to (∑π₂ trivial-structure))))

          𝔻-at_as-point-in-BAut-𝔻ₑ :
            ∀ (x : M) → BAut 𝔻ₑ
          𝔻-at_as-point-in-BAut-𝔻ₑ x =
            (𝔻-at x , ∥→ (λ z → (∗ , univalence (z ⁻¹≃))) ∥→  (all-𝔻s-are-merely-equivalent x))

          triangle-from-the-G-structure-at :
            ∀ (x : M) → triangles-at (𝔻-at x as-point-in-BAut-𝔻ₑ)
          triangle-from-the-G-structure-at x =
            (lift-of-g ∘ ι-𝔻 x , (χ-M ∘ ι-𝔻 x , (pre-whisker (ι-𝔻 x) to homotopy)))

        in  ∀ (x : M)
          → ∀ (γ : 𝔻-at x as-point-in-BAut-𝔻ₑ ≈ e-BAut 𝔻ₑ)
          → ∥ transport triangles-at γ (triangle-from-the-G-structure-at x)
              ≈ triangle-of-the-trivial-G-structure ∥


    {-
      Show that the trivial structure on V is torision free.
    -} {-
    module basic-calculations where
      open torsion-free-structures (homogeneous-space-as-manifold V)

      calculate-triangle-transport :
        ∀ {𝔻′ : BAut 𝔻ₑ} -- (Δ : triangles-at 𝔻′)
       →  {!!} -- → transport triangles-at Δ ≈ ?

      calculate-triangle-transport = {!!}

      result : trivial-structure is-torsion-free
      result x y = ∣ {!!} ∣
  -}
-}
