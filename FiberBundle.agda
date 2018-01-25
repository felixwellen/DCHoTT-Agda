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
  open import OneImage
  open import DependentTypes
  open import InfinityGroups


  {- 
    we start with the most natural definition
    in a type theoretic setting 
  
    everything else in this file, 
    is about linking this definition 
    with definitions looking more like
    what is common in pure mathematics
    
  -}

  record _is-a_-fiber-bundle {B : 𝒰} (φ : B → 𝒰) (F : 𝒰) : 𝒰₁ where
    field
      all-fibers-are-merely-equivalent : ∀ (b : B) → ∥ φ b ≃ F ∥

    canonical-cover′ : B → 𝒰
    canonical-cover′ b = φ b ≃ F

    canonical-cover : ∑ canonical-cover′ → B
    canonical-cover (F′ , _) = F′

  record _is-a⁗_-fiber-bundle⁗ {E B : 𝒰} (p : E → B) (F : 𝒰) : 𝒰₁ where
    field
      χ : B → BAut F
      classyfies : equivalence-of (λ b → fiber-of p at b) and (universal-family-over-BAut′ F) over χ
      
  -- product property expressed by pullback square
  _is-a-product-with-projections_and_ :
    ∀ {A B : U₀} (Z : U₀) (z₁ : Z → A) (z₂ : Z → B)
    → U₀
  Z is-a-product-with-projections z₁ and z₂ =
    pullback-square-with-right (λ a → ∗)
        bottom (λ b → ∗)
        top z₁
        left z₂

  _is-a-product-of_and_ :
    (Z A B : U₀) → U₀
  Z is-a-product-of A and B =
    ∑ (λ (z₁ : Z → A) →
    ∑ (λ (z₂ : Z → B) → Z is-a-product-with-projections z₁ and z₂))

  _*_ : ∀ {E B B′ : U₀}
    → (f : B′ → B) → (φ : E → B) → U₀
  f * φ = upper-left-vertex-of (complete-to-pullback-square φ f)
  
  _*→_ : ∀ {E B B′ : U₀}
    → (f : B′ → B) → (φ : E → B) → ((f * φ) → B′)
  f *→ φ = left-map-of (complete-to-pullback-square φ f)

  ^ = underlying-map-of-the-1-epimorphism


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

  record _is-a‴_-fiber-bundle‴ {E B : U₀} (φ : E → B) (F : U₀) : U₁ where
    field
      V : U₀
      v : V ↠ B
      v′ : V × F → E
      □ : pullback-square-with-right φ
            bottom (underlying-map-of-the-1-epimorphism v)
            top v′
            left π₁

  {- a variant -}

  record _is-a′_-fiber-bundle′ {E B : U₀} (φ : E → B) (F : U₀) : U₁ where
    constructor on_the-pullback-along_is-trivial-by_and_
    field
      V : U₀
      covering : V ↠ B
      projection-to-the-fiber : (^ covering * φ) → F
      the-pullback-is-a-product :
          (^ covering * φ) is-a-product-with-projections
            projection-to-the-fiber and (^ covering *→ φ) 


  

  covering-as-map : 
    ∀ {E B F : U₀} {φ : E → B} (φ-as-bundle : φ is-a′ F -fiber-bundle′)
    → _is-a′_-fiber-bundle′.V φ-as-bundle → B
  covering-as-map φ-as-bundle = ^ (_is-a′_-fiber-bundle′.covering φ-as-bundle)

  -- project to the square drawn in the comment above
  covering-pullback-square :
    ∀ {E B F : U₀} {φ : E → B} (φ-as-bundle : φ is-a′ F -fiber-bundle′)
    → pullback-square-with-right φ
       bottom (covering-as-map φ-as-bundle)
       top _
       left ((covering-as-map φ-as-bundle) *→ φ)
  covering-pullback-square {_} {_} {_} {φ} φ-as-bundle = 
    complete-to-pullback-square φ (covering-as-map φ-as-bundle) 


  {-
    a dependent version of the above
  -}

  record _is-a″_-fiber-bundle″ {B : 𝒰} (φ : B → 𝒰) (F : 𝒰) : 𝒰₁ where 
    field
      V : U₀
      v : V ↠ B
      pullback-trivializes : (x : V) → φ(v $↠ x) ≃ F


  module logical-equivalences-between-the-four-definitions-of-fiber-bundles
    {B F : 𝒰} where

    def‴-to-def″ : ∀ {E : 𝒰} (p : E → B)
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

    def″-to-def‴ : ∀ (φ : B → 𝒰)
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
      ∀ (φ : B → 𝒰)
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
          λ x → ∥→ step1 x ∥→ ((proof-that v is-1-epi) x)
        }


    def-to-def″ :
      ∀ (φ : B → 𝒰)
      → φ is-a F -fiber-bundle
      → φ is-a″ F -fiber-bundle″
    def-to-def″ φ
      φ-is-a-fiber-bundle =
      let
        open _is-a_-fiber-bundle φ-is-a-fiber-bundle
      in record
         {
           V = _ ;
           v = canonical-cover is-1-epi-by
             (λ b →
               ∥≃ fiber-of-a-∑ {P = canonical-cover′} b ∥≃ ⁻¹≃
                 $≃ (all-fibers-are-merely-equivalent b) ) ;
           pullback-trivializes = ∑π₂
         }

    open import Univalence
    open import Sums

    private
      specialize-image-to-BAut : ∀ (φ : B → 𝒰)
        → (x : B) → ∥ (φ x ≃ F) ∥ → the-1-image-of (λ ∗ → F) contains (φ x)
      specialize-image-to-BAut φ x = ∥→ (λ e → (∗ , univalence (e ⁻¹≃))) ∥→
      specialize-image-to-BAut′ : ∀ (φ : B → 𝒰)
        → (x : B) → the-1-image-of (λ ∗ → F) contains (φ x) → ∥ (φ x ≃ F) ∥ 
      specialize-image-to-BAut′ φ x = ∥→ (λ {(∗ , p) → U-transport p ⁻¹≃}) ∥→

    def-to-def⁗ :
      ∀ (φ : B → 𝒰)
      → φ is-a F -fiber-bundle
      → (∑π₁-from φ) is-a⁗ F -fiber-bundle⁗
    def-to-def⁗ φ
      record { all-fibers-are-merely-equivalent = all-fibers-are-merely-equivalent } =
      record
      {
        χ = λ x → ((φ x) , specialize-image-to-BAut φ x (all-fibers-are-merely-equivalent x)) ;
        classyfies = λ x → fiber-of-a-∑ x
      }

    def⁗-to-def :
      ∀ {E : 𝒰} (p : E → B)
      → p is-a⁗ F -fiber-bundle⁗
      → (λ x → fiber-of p at x) is-a F -fiber-bundle
    def⁗-to-def p
      record { χ = χ ; classyfies = classyfies } =
      record
      {
        all-fibers-are-merely-equivalent = λ b →
        specialize-image-to-BAut′ (λ x → fiber-of p at x) b
          (U-transport ((λ z → the-1-image-of _ contains z) ⁎ univalence (classyfies b) ) ⁻¹≃ $≃ (∑π₂ (χ b)))
      }


  -- obsolete proof, soon to be replaced
  module all-fiber-bundle-are-associated 
          {E B F : U₀} (φ : E → B) (φ-is-a-fiber-bundle : φ is-a′ F -fiber-bundle′) where
         
         {-

           take the pullback-square witnessing the local triviality of φ
    
           v*E ───→ E
            | ⌟     |
           v*φ      φ
            ↓       ↓
            V ──v─↠ B
         
         -}

         open _is-a′_-fiber-bundle′ φ-is-a-fiber-bundle

         v = covering-as-map φ-is-a-fiber-bundle
         v*φ = v *→ φ 

         covering-square : 
           pullback-square-with-right φ
             bottom v
             top _
             left v*φ
         covering-square = 
           covering-pullback-square φ-is-a-fiber-bundle
             
         {-

           ... and the product square for v*E:
    
           v*E ─p─→ F
            | ⌟     |
           v*φ      |
            ↓       ↓
            V ────→ 1
     
         -}
         
         v*E = v * φ
         p : v*E → F
         p = projection-to-the-fiber

         product-square-for-v*E = the-pullback-is-a-product

         {- 
           switch to classifying maps, i.e. get:

           1 ←─ V ─→ B
            \   |   /
             \  |  /
              ↘ ↓ ↙ 
                U
         -}

         left-triangle : dependent-replacement v*φ ⇒ dependent-replacement (λ (x : F) → ∗) ∘ (λ (x : V) → ∗)
         left-triangle = 
           pullbacks-are-fiberwise-equivalences.as-triangle-over-the-universe 
             product-square-for-v*E

         right-triangle : dependent-replacement v*φ ⇒ dependent-replacement φ ∘ v
         right-triangle = 
           pullbacks-are-fiberwise-equivalences.as-triangle-over-the-universe 
             covering-square

         {-
           compose with 
           
               1─────→ U
                \     ↗
                 ↘   / χ
                BAut(F)

           to get a epi/mono-square:

             V ──1─→ BAut F
             |         |
       (epi) v         χ (mono)
             ↡         ↓
             B ───φ──→ U
           
        -}

         χ : BAut F → U₀
         χ = ι-BAut F

         the-square-commutes : χ ∘ (λ (_ : V) → (F , ∣ (∗ , refl) ∣ )) ⇒ (dependent-replacement φ) ∘ v
         the-square-commutes x = χ (F , ∣ ∗ , refl ∣)
                                ≈⟨ refl ⟩
                                 F
                                ≈⟨ replacement-over-One-is-constant (λ (x₁ : F) → ∗) ⁻¹ ⟩
                                 dependent-replacement (λ (x₁ : F) → ∗) ∗
                                ≈⟨ left-triangle x ⁻¹ ⟩
                                 dependent-replacement v*φ x
                                ≈⟨ right-triangle x ⟩
                                 (dependent-replacement φ ∘ v) x ≈∎
        {-
        
        get the diagonal

        -}

         

         diagonal : B → BAut F
         diagonal = 1-mono/1-epi-lifting.lift
                     χ (dependent-replacement φ) (λ x → (F , ∣ (∗ , refl) ∣ )) v
                     ι-BAut-is-1-mono (proof-that covering is-1-epi)
                     the-square-commutes

         classifying-morphism = diagonal


       {-
         the diagonal is a morphism over U₀

            B ───→ BAut F
             \    /
              \  /
               U₀

       -}

         as-U₀-morphism :
           dependent-replacement φ ⇒ χ ∘ diagonal
         as-U₀-morphism = 1-mono/1-epi-lifting.lower-triangle χ (dependent-replacement φ)
                            (λ x → F , ∣ ∗ , refl ∣) v ι-BAut-is-1-mono
                            proof-that covering is-1-epi
                            the-square-commutes ⁻¹⇒


       {-
         as a by product, we know that all fibers of the bundle
         are merely equivalent to F

       -}

         all-fibers-are-merely-equivalent :
           ∀ (b : B)
           → ∥ F ≃ fiber-of φ at b  ∥
         all-fibers-are-merely-equivalent b =
           let
             F′-in-BAut : U₀
             F′-in-BAut = ∑π₁ (diagonal b)
             ∣F′≃F∣ : ∥ F ≃ F′-in-BAut ∥
             ∣F′≃F∣ = ∥→ (transport-as-equivalence (λ (A : U₀) → A))  ∥→
                      ( ∥→ ∑π₂-from (λ ∗ → F ≈ F′-in-BAut) ∥→ ((∑π₂ (diagonal b))))
             -- now, use the homotopy from above to see
             --    fiber-of φ at b ≃ F′-in-BAut
             fiber≃F′ : fiber-of φ at b ≃ F′-in-BAut
             fiber≃F′ = (transport-as-equivalence (λ (A : U₀) → A)) (as-U₀-morphism b)
           in ∥→ (λ f → fiber≃F′ ⁻¹≃ ∘≃ f) ∥→ ∣F′≃F∣



  {-
     the last statement in the module above is also sufficient:
  -}

  {-
  maps-with-merely-equivalent-are-fiber-bundles : 
    ∀ {B E F : 𝒰} (φ : E → B) 
    → (∀ (b : B) → ∥ F ≃ fiber-of φ at b  ∥) 
    → φ is-a′ F -fiber-bundle′
  maps-with-merely-equivalent-are-fiber-bundles φ all-fibers-are-equivalent =
    on {!!} the-pullback-along {!!} is-trivial-by {!!} and {!!}
  -}
