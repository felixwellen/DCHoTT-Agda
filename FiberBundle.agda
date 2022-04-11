{-# OPTIONS --without-K #-}

module FiberBundle where
  open import Basics
  open import EqualityAndPaths
  open import PropositionalTruncation
  open import PullbackSquare
  open import Homotopies
  open import Equivalences
  open import Fiber
  open import Language
  open import Image
  open import DependentTypes
  open import InfinityGroups


  {-
    we start with the most natural definition
    in a type theoretic setting

    everything else in this file,
    is about linking this definition
    with definitions looking more like
    what is common in mathematics

  -}

  record _is-a_-fiber-bundle {B : 𝒰₀} (φ : B → 𝒰₀) (F : 𝒰₀) : 𝒰₀ where
    field
      all-fibers-are-merely-equivalent : ∀ (b : B) → ∥ φ b ≃ F ∥

    canonical-cover′ : B → 𝒰₀
    canonical-cover′ b = φ b ≃ F

    canonical-cover : ∑ canonical-cover′ → B
    canonical-cover (F′ , _) = F′

  record _is-a′_-fiber-bundle′ {E B : 𝒰₀} (p : E → B) (F : 𝒰₀) : 𝒰₁ where
    field
      χ : B → BAut F
      classyfies : equivalence-of (λ b → fiber-of p at b) and (universal-family-over-BAut′ F) over χ


  classifying-morphism′ : {E B : 𝒰₀} {p : E → B} {F : 𝒰₀}
    → p is-a′ F -fiber-bundle′
    → B → BAut F
  classifying-morphism′ is-fiber-bundle =
    let open _is-a′_-fiber-bundle′ is-fiber-bundle
    in χ


  -- product property expressed by pullback square
  _is-a-product-with-projections_and_ :
    ∀ {A B : 𝒰₀} (Z : 𝒰₀) (z₁ : Z → A) (z₂ : Z → B)
    → 𝒰₀
  Z is-a-product-with-projections z₁ and z₂ =
    pullback-square-with-right (λ a → ∗)
        bottom (λ b → ∗)
        top z₁
        left z₂

  _is-a-product-of_and_ :
    (Z A B : 𝒰₀) → 𝒰₀
  Z is-a-product-of A and B =
    ∑ (λ (z₁ : Z → A) →
    ∑ (λ (z₂ : Z → B) → Z is-a-product-with-projections z₁ and z₂))

  _*_ : ∀ {E B B′ : 𝒰₀}
    → (f : B′ → B) → (φ : E → B) → 𝒰₀
  f * φ = upper-left-vertex-of (complete-to-pullback-square φ f)

  _*→_ : ∀ {E B B′ : 𝒰₀}
    → (f : B′ → B) → (φ : E → B) → ((f * φ) → B′)
  f *→ φ = left-map-of (complete-to-pullback-square φ f)

  ^ = underlying-map-of-the-surjection


  {-
    A more standard-mathematical way:

    a fiber bundle φ : E → B is required to be locally trivial,
    which might be witnessed by a pullback square like this:

    V×F ───→ E
     | ⌟     |
    v*φ      φ
     ↓       ↓
     V ──v─↠ B

  -}

  record _is-a‴_-fiber-bundle‴ {E B : 𝒰₀} (φ : E → B) (F : 𝒰₀) : 𝒰₁ where
    field
      V : 𝒰₀
      v : V ↠ B
      v′ : V × F → E
      □ : pullback-square-with-right φ
            bottom (underlying-map-of-the-surjection v)
            top v′
            left π₁


  {-
    a dependent version of the above
  -}

  record _is-a″_-fiber-bundle″ {B : 𝒰₀} (φ : B → 𝒰₀) (F : 𝒰₀) : 𝒰₁ where
    field
      V : 𝒰₀
      v : V ↠ B
      pullback-trivializes : (x : V) → φ(v $↠ x) ≃ F


  module logical-equivalences-between-the-four-definitions-of-fiber-bundles
    {B F : 𝒰₀} where

    def‴-to-def″ : ∀ {E : 𝒰₀} (p : E → B)
      → p is-a‴ F -fiber-bundle‴
      → (λ b → fiber-of p at b) is-a″ F -fiber-bundle″
    def‴-to-def″ p record { V = V ; v = v ; v′ = v′ ; □ = □ } =
      let
        open pullbacks-are-fiberwise-equivalences □
      in record
         {
                V = V ;
                v = v ;
                pullback-trivializes = λ x → fiber-of-π₁-is-second-factor x ∘≃ (equivalence-at x) ⁻¹≃
         }

    def″-to-def‴ : ∀ (φ : B → 𝒰₀)
      → φ is-a″ F -fiber-bundle″
      → (∑π₁-from φ) is-a‴ F -fiber-bundle‴
    def″-to-def‴ φ
      record { V = V ; v = v ; pullback-trivializes = pullback-trivializes } =
      let
        as-fiberwise-morphism : morphism-of-dependent-types _ _ (λ _ → F) φ
        as-fiberwise-morphism =
          record
          {
            base-change = v ↠→  ;
            morphism-of-fibers = λ x → (pullback-trivializes x ⁻¹≃) ≃→
          }
        open fiberwise-equivalences-are-pullbacks
          as-fiberwise-morphism
          (λ x → proof-of-equivalency (pullback-trivializes x ⁻¹≃))
      in record { V = V ; v = v ; v′ = glued-morphism ; □ = fiberwise-equivalences-are-pullbacks }


    def″-to-def :
      ∀ (φ : B → 𝒰₀)
      → φ is-a″ F -fiber-bundle″
      → φ is-a F -fiber-bundle
    def″-to-def φ
      record { V = V ; v = v ; pullback-trivializes = pullback-trivializes } =
      let
        step1 : (x : B) → (y : fiber-of (v ↠→) at x) → φ x ≃ F
        step1 x = λ {(y is-in-the-fiber-by γ) →
                     pullback-trivializes y ∘≃ transport-as-equivalence φ γ ⁻¹≃}
      in record
        {
          all-fibers-are-merely-equivalent =
          λ x → ∥→ step1 x ∥→ ((proof-that v is-surjective) x)
        }


    def-to-def″ :
      ∀ (φ : B → 𝒰₀)
      → φ is-a F -fiber-bundle
      → φ is-a″ F -fiber-bundle″
    def-to-def″ φ
      φ-is-a-fiber-bundle =
      let
        open _is-a_-fiber-bundle φ-is-a-fiber-bundle
      in record
         {
           V = _ ;
           v = canonical-cover is-surjective-by
             (λ b →
               ∥≃ fiber-of-a-∑ {P = canonical-cover′} b ∥≃ ⁻¹≃
                 $≃ (all-fibers-are-merely-equivalent b) ) ;
           pullback-trivializes = ∑π₂
         }


    open import Univalence
    open import Sums

    private
      specialize-image-to-BAut : ∀ (φ : B → 𝒰₀)
        → (x : B) → ∥ (φ x ≃ F) ∥ → the-image-of (λ ∗ → F) contains (φ x)
      specialize-image-to-BAut φ x = ∥→ (λ e → (∗ , univalence (e ⁻¹≃))) ∥→

      point-to-F : 𝟙 → 𝒰₀
      point-to-F _ = F

      specialize-image-to-BAut′ : ∀ (φ : B → 𝒰₀)
        → (x : B) → the-image-of point-to-F contains (φ x) → ∥ (φ x ≃ F) ∥
      specialize-image-to-BAut′ φ x = ∥→ (λ {(∗ , p) → U-transport p ⁻¹≃}) ∥→

    abstract
      def-to-def′ :
        ∀ (φ : B → 𝒰₀)
        → φ is-a F -fiber-bundle
        → (∑π₁-from φ) is-a′ F -fiber-bundle′
      def-to-def′ φ
        record { all-fibers-are-merely-equivalent = all-fibers-are-merely-equivalent } =
        record
        {
          χ = λ x → ((φ x) , specialize-image-to-BAut φ x (all-fibers-are-merely-equivalent x)) ;
          classyfies = λ x → fiber-of-a-∑ x
        }


      def′-to-def :
        ∀ {E : 𝒰₀} (p : E → B)
        → p is-a′ F -fiber-bundle′
        → (λ x → fiber-of p at x) is-a F -fiber-bundle
      def′-to-def p
        record { χ = χ ; classyfies = classyfies } =
        record
        {
          all-fibers-are-merely-equivalent = λ b →
          specialize-image-to-BAut′ (λ x → fiber-of p at x) b
            (U-transport ((λ z → the-image-of _ contains z) ⁎ univalence (classyfies b) ) ⁻¹≃ $≃ (∑π₂ (χ b)))
        }

      compute-classifying-morphism :
        {ϕ : B → 𝒰₀}
        → (ϕ-is-fiber-bundle : ϕ is-a F -fiber-bundle)
        → let is-fiber-bundle′ = def-to-def′ ϕ ϕ-is-fiber-bundle
          in ι-BAut F ∘ classifying-morphism′ is-fiber-bundle′ ⇒ ϕ
      compute-classifying-morphism ϕ-is-fiber-bundle x = refl
