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
  open import OneImage
  open import EtaleMaps
  open import Manifolds
  open import SymmetricSpace
  open import FormalDisk
  open import HomogeneousType

  formal-disk-of :
    ∀ {V : 𝒰₀}
    → (structure-on-V : homogeneous-structure-on V)
    → 𝒰₀
  formal-disk-of structure-on-V =
    formal-disk-at (homogeneous-structure-on_.e structure-on-V)
  
  record groups-over-structure-group-of_ {V : 𝒰₀}
    (structure-on-V : homogeneous-structure-on V) : 𝒰₁ where
    constructor group-given-by-delooping_with-unit_and-morphism_with-unit-identification_
    field
      BG : 𝒰₀
      Be : BG
      Bφ : BG → BAut (formal-disk-of structure-on-V)
      path-between-units : Bφ(Be) ≈ e-BAut (formal-disk-of structure-on-V)


  module G-structures-on-V-manifolds
    {V′ M U : 𝒰₀} (w : U ─ét→ M) (v : U ─ét→ V′)
    (V : homogeneous-structure-on V′)
    (reduction : groups-over-structure-group-of V)
    (M-is-a-manifold : M is-a-manifold-with-cover w
                      locally-like V by v) where
    

    open homogeneous-structure-on_ V
    open groups-over-structure-group-of_ reduction

    De = formal-disk-at e

    χ : M → BAut De
    χ = the-formal-disk-bundle-on-a-manifold-is-a-fiber-bundle.classifying-morphism
        U M w V v M-is-a-manifold

    {-
      Let BG be a delooping of a group G
      together with an 'inclusion' Bι : BG → BAut(D)
      into the Automorphisms of the formal disk 
      at the unit of V.
      A G-structure on a V-manifold M is given by a
      lift of the classifying morphism of T∞ V
      along Bι:
  
         ↗ BG 
        φ   |
       /   Bφ
      /     ↓ 
      M ─→ BAut(D)
  
      We do not claim, that the type of those lifts
      is the correct moduli type of G-structures on M.
    -}

    G-structures : U₁
    G-structures = ∑ (λ (φ : M → BG) → Bφ ∘ φ ⇒ χ)
    

  {-
      on a left invertible H-space V,
      there is always a 1-structure (for the trivial group 1)
  -}
  module trivial-structure-on-left-homogeneous-types
    {V′ : 𝒰}
    (V : homogeneous-structure-on V′) 
    (group-over-BAutD : groups-over-structure-group-of V)
    where

    open homogeneous-structure-on_ V

    𝔻ₑ = formal-disk-at e

    G-structures-on-V : 𝒰₁
    G-structures-on-V =
      G-structures-on-V-manifolds.G-structures
      id-as-étale-map id-as-étale-map
      V
      group-over-BAutD
      (left-invertible-H-spaces-are-manifolds V)

    φ : (x : V′) → 𝔻ₑ ≃ 𝔻 _ x
    φ = triviality-of-the-formal-disk-bundle-over-homogeneous-types.identifications-of-all-formal-disks V

    open groups-over-structure-group-of_ group-over-BAutD

    -- calculate the classifying morphism for V′
    -- i.e. give an explicit description
    χ-V′ : V′ → BAut 𝔻ₑ
    χ-V′ x = ((formal-disk-at x) , ∣ (∗ , univalence (φ x)) ∣)

    V-is-a-manifold = (left-invertible-H-spaces-are-manifolds V)

    χ′ = G-structures-on-V-manifolds.χ id-as-étale-map id-as-étale-map
              V group-over-BAutD
              V-is-a-manifold
    χ-V′⇒χ′ :
      χ-V′ ⇒ χ′
    χ-V′⇒χ′ = 1-monos-are-monos χ-V′ χ′ (ι-BAut 𝔻ₑ) (ι-im₁-is-1-mono (λ ∗₃ → 𝔻ₑ))
      (λ (x : V′) →
           the-formal-disk-bundle-on-a-manifold-is-a-fiber-bundle.commutes-with-the-dependent-replacement-of-T∞
           V′ V′ id-as-étale-map V id-as-étale-map V-is-a-manifold
           x)

    trivial-structure : G-structures-on-V
    trivial-structure =
      ((λ x → Be) , (λ x →
         Bφ(Be)
        ≈⟨ path-between-units ⟩
          e-BAut _
        ≈⟨ 1-monos-are-monos (λ _ → e-BAut _) χ-V′ (ι-BAut 𝔻ₑ)
             (ι-im₁-is-1-mono (λ ∗₃ → 𝔻ₑ)) (λ y → univalence (φ y)) x ⟩
          χ-V′ x
        ≈⟨ χ-V′⇒χ′ x ⟩
          χ′ x
        ≈∎))

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

    {-
      now, for a general V-manifold
    -}
    module general-manifolds
      {M U : 𝒰₀} (w : U ─ét→ M) (v : U ─ét→ V′)
      (M-is-a-V-manifold : M is-a-manifold-with-cover w
                      locally-like V by v)
                 where

      ∗𝔻 : (x₀ : M) → formal-disk-at x₀
      ∗𝔻 x₀ = (x₀ , refl) 

      χ-M : M → BAut 𝔻ₑ
      χ-M =
        the-formal-disk-bundle-on-a-manifold-is-a-fiber-bundle.classifying-morphism
          U M w V v M-is-a-V-manifold
      
      all-𝔻s-are-merely-equivalent :
        ∀ (x : M)
        → ∥  𝔻ₑ ≃ 𝔻-at x ∥
      all-𝔻s-are-merely-equivalent x =
        the-formal-disk-bundle-on-a-manifold-is-a-fiber-bundle.all-formal-disks-are-merely-equivalent
          U M w V v M-is-a-V-manifold x 
      
      G-structures-on-M =
        G-structures-on-V-manifolds.G-structures
        w v V group-over-BAutD M-is-a-V-manifold

      _is-torsion-free :
        G-structures-on-M → U₁
      (lift , homotopy) is-torsion-free =
        {- 
          to decide if a G-structure is torsion free,
          we have to compare it locally to the trivial G-structure.
          This means comparing all triangles obtained by restricting the
          G-Structure to the formal disk at some point x
          
  
                ↗ BG                       ↗ BG       
               /   |                      φ   |       
              /   Bφ         ≈           /   Bφ       
             /     ↓                    /     ↓       
          D x ──→ BAut(De)     D x ──→ M ──→ BAut(De) 

          to the De-triangle of the trivial G-Structure 

                ↗ BG       
              B1   |       
              /   Bφ       
             /     ↓       
          D e ──→ BAut(De) 

        -}
        let
          -- classifying map of T∞V
          ξ = G-structures-on-V-manifolds.χ id-as-étale-map id-as-étale-map
              V group-over-BAutD
              V-is-a-manifold

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
            (𝔻-at x , ∥→ (λ z → (∗ , univalence z)) ∥→  (all-𝔻s-are-merely-equivalent x))

          triangle-from-the-G-structure-at :
            ∀ (x : M) → triangles-at (𝔻-at x as-point-in-BAut-𝔻ₑ)
          triangle-from-the-G-structure-at x =
            (lift ∘ ι-𝔻 x , (χ-M ∘ ι-𝔻 x , (pre-whisker (ι-𝔻 x) to homotopy)))

        in  ∀ (x : M)
          → ∀ (γ : 𝔻-at x as-point-in-BAut-𝔻ₑ ≈ e-BAut 𝔻ₑ)
          → ∥ transport triangles-at γ (triangle-from-the-G-structure-at x)
              ≈ triangle-of-the-trivial-G-structure ∥ 
