{-# OPTIONS --without-K #-}

module Image where 
  open import Basics
  open import Language
  open import EqualityAndPaths
  open import Homotopies
  open import Fiber
  open import Equivalences renaming (underlying-map-of to underlying-map-of-the-equivalence)
  open import EquivalenceCharacterization
  open import Contractibility
  open import PropositionalTruncation
  open import Univalence

  {-
    the following is called 'surjective' in the HoTT-Book 
    (at least if A and B are Sets)
  -}
  
  _is-surjective : 
    ∀ {i} {j} {A : U i} {B : U j}
    → (A → B) → U (i ⊔ j)
  _is-surjective {_} {_} {A} {B} f = (b : B) → ∥ fiber-of f at b ∥

  record _↠_ {i} {j} (A : U i) (B : U j) : U (i ⊔ j) where
    constructor _is-surjective-by_
    field
      morphism : A → B
      proof-that-it-is-surjective : morphism is-surjective

  underlying-map-of-the-surjection : 
    ∀ {i} {j} {A : U i} {B : U j}
    → (f : A ↠ B) → (A → B)
  underlying-map-of-the-surjection
    (morphism is-surjective-by proof-that-it-is-surjective) = morphism

  _$↠_ : ∀ {A B : 𝒰₀}
    → (f : A ↠ B) → A → B
  f $↠ a = (underlying-map-of-the-surjection f) a

  _↠→ : ∀ {A B : 𝒰₀}
    → (f : A ↠ B) → (A → B)
  f ↠→ = λ a → f $↠ a
  
  proof-that_is-surjective :
    ∀ {A B : 𝒰₀}
    → (f : A ↠ B) → (underlying-map-of-the-surjection f) is-surjective
  proof-that (_ is-surjective-by proof) is-surjective = proof
    

  the-image-of_contains : 
    ∀ {i j} {A : U i} {B : U j} 
    → (f : A → B) → (B → U (i ⊔ j))
  the-image-of f contains b = ∥ ∑ (λ a → f(a) ≈ b) ∥

  to-point-in-truncated-fiber : 
    ∀ {i} {j} {A : U i} {B : U j} {f : A → B} {b : B}
    → ∥ ∑ (λ a → f(a) ≈ b) ∥ → ∥ fiber-of f at b ∥
  to-point-in-truncated-fiber {_} {_} {_} {_} {f} {b} = 
    ∥-∥-recursion (∥ fiber-of f at b ∥) (∥-∥-is-truncation _) (λ {(a , γ) → ∣ a is-in-the-fiber-by γ ∣ }) 

  from-point-in-truncated-fiber : 
    ∀ {A B : 𝒰₀} {f : A → B} {b : B}
    → ∥ fiber-of f at b ∥ → ∥ ∑ (λ a → f(a) ≈ b) ∥
  from-point-in-truncated-fiber =
    ∥-∥-recursion (∥ _ ∥) (∥-∥-is-truncation _) (λ {(a is-in-the-fiber-by γ) → ∣ (a , γ) ∣ }) 

  image :
    ∀ {i j} {A : U i} {B : U j} 
    → (f : A → B) → U (i ⊔ j)
  image f = ∑ (λ b → the-image-of f contains b)

  im₁ = image

  the-induced-map-from-the-image-of_to-the-codomain :
    ∀ {i j} {A : U i} {B : U j} 
    → (f : A → B) → (image f → B)
  the-induced-map-from-the-image-of f to-the-codomain (b , x) = b
  
  ι-im₁ = the-induced-map-from-the-image-of_to-the-codomain

  the-induced-map-from-the-domain-to-the-image-of :
    ∀ {i} {j} {A : U i} {B : U j} 
    → (f : A → B) → (A → image f)
  the-induced-map-from-the-domain-to-the-image-of f a = 
    (f(a) , ∣ (a , refl ) ∣ )

  π-im₁ = the-induced-map-from-the-domain-to-the-image-of

  {-

    A ─f─→ B
     \    ↗ 
      π  ι    => (fiber-of f → fiber-of π)
       ↘/
       im₁
  -}

  π-im₁-is-surjective : 
    ∀ {i j}  {A : U i} {B : U j} (f : A → B) 
    → (π-im₁ f is-surjective)
  π-im₁-is-surjective f (b , p) = 
    let
      truncated-fiber-of-π = ∥ fiber-of (π-im₁ f) at (b , p) ∥
      map-on-fibers : fiber-of f at b → truncated-fiber-of-π
      map-on-fibers = λ {(a is-in-the-fiber-by γ) 
                      → ∣ (a is-in-the-fiber-by (
                         (f(a) , ∣ (a , refl) ∣ ) 
                        ≈⟨ equality-action-on-∑ (f a) b γ (∣ (a , refl) ∣)  ⟩ 
                         (b , transport (λ b → ∥ ∑ (λ a → f(a) ≈ b) ∥) γ (∣ (a , refl) ∣)) 
                        ≈⟨ (λ p′ → (b , p′)) ⁎ -1-truncated _ p  ⟩ 
                         (b , p) 
                        ≈∎)) ∣ }
    in ∥-∥-recursion 
         truncated-fiber-of-π (∥-∥-is-truncation _) map-on-fibers (to-point-in-truncated-fiber p)
    
  -- one example...
  equivalences-are-surjective :
    ∀ {A B : 𝒰₀} (f : A ≃ B)
    → (underlying-map-of-the-equivalence f) is-surjective
  equivalences-are-surjective f b =
    ∣ (right-inverse-of-the-equivalence f b) is-in-the-fiber-by (counit-of-the-equivalence f b ⁻¹) ∣ 

  _is-injective′ : 
    ∀ {i} {A B : U i} 
    → (f : A → B) → U i
  f is-injective′ = (x y : _) → f x ≈ f y → x ≈ y

  _is-injective : 
    ∀ {i} {j} {A : U i} {B : U j} 
    → (f : A → B) → U (i ⊔ j)
  f is-injective = Π (λ b → (fiber-of f at b) is-a-proposition)

  ι-im₁-is-injective : 
    ∀ {i} {j} {A : U i} {B : U j} (f : A → B)
    → ι-im₁ f is-injective 
  ι-im₁-is-injective f b = (the-proposition (λ (A : _) → A is-a-proposition)
                            is-equivalence-invariant-by-univalence (fiber-of-a-∑ b ⁻¹≃))
                             (∥-∥-is-truncation (∑ (λ a → f a ≈ b)))


  injectives-are-monos :
    ∀ {i j k} {A : U i} {B : U j} {C : U k} (f g : A → B) (m : B → C)
    → m is-injective → m ∘ f ⇒ m ∘ g
    → f ⇒ g    
  injectives-are-monos f g m m-is-injective H a =
    let
      fa-as-point-in-the-fiber : fiber-of m at (m(g a))
      fa-as-point-in-the-fiber = f a is-in-the-fiber-by H a
      ga-as-point-in-the-fiber : fiber-of m at (m(g a))
      ga-as-point-in-the-fiber = g a is-in-the-fiber-by refl
      fa≈ga : fa-as-point-in-the-fiber ≈ ga-as-point-in-the-fiber
      fa≈ga = m-is-injective (m (g a)) fa-as-point-in-the-fiber
                ga-as-point-in-the-fiber
      
    in ι-fiber ⁎ fa≈ga

  

  a-injectiveism-factoring-over-the-point-is-trivial :
    ∀ {A B : 𝒰₀} (f : A → B)
    → (f is-injective′)
    → ∑ (λ b → f ⇒ (λ _ → b))
    → A is-a-proposition
  a-injectiveism-factoring-over-the-point-is-trivial f f-is-mono (b , H) =
    λ a a′ → f-is-mono a a′ (H a • H a′ ⁻¹)


{-
   injective/surjective lifting
   
   given a commutative square:
     
     A ─f─→ X
     |      |
     e      m
     ↓      ↓
     B ─g─→ Y
   
   with m injective and e surjective there is a 
   diagonal lift
-}

  module injective/surjective-lifting
         {i}
         {A B : 𝒰₀} {X Y : U i}
         (m : X → Y) (g : B → Y)
         (f : A → X) (e : A → B)
         (m-is-injective : m is-injective) (e-is-surjective : e is-surjective)
         (H : m ∘ f ⇒ g ∘ e)
         where
         
    {- idea: take a 'b : B' and map it to x in the 
             propositional truncation of the fiber 
             over b, given by the assumption that 
             e is surjective. map x to the fiber over
             g(b), which is possible because m is 
             injective.
    -}
    
    map-to-the-fiber : (b : B) → fiber-of e at b → fiber-of m at g(b)
    map-to-the-fiber b = λ {(a is-in-the-fiber-by γ) → f(a) is-in-the-fiber-by (H a • g ⁎ γ)}
    induced-map-on-the-truncated-fiber : (b : B) → ∥ fiber-of e at b ∥ → fiber-of m at g(b)
    induced-map-on-the-truncated-fiber b = 
        ∥-∥-recursion 
          (fiber-of m at g(b)) 
          (m-is-injective (g b)) 
          (map-to-the-fiber b)
          
    private      
      lift-of-g : (B → X)
      lift-of-g b = as-point-in-the-domain (induced-map-on-the-truncated-fiber b (e-is-surjective b))

  
    upper-triangle : f ⇒ lift-of-g ∘ e 
    upper-triangle a = as-point-in-the-domain ⁎ 
                          (f (a) is-in-the-fiber-by _ 
                         ≈⟨ refl ⟩ 
                          induced-map-on-the-truncated-fiber (e a) (∣ a is-in-the-fiber-by refl ∣) 
                         ≈⟨ (λ x → induced-map-on-the-truncated-fiber (e a) x) ⁎ 
                             -1-truncated (∣ a is-in-the-fiber-by refl ∣) (e-is-surjective (e a)) ⟩  
                          induced-map-on-the-truncated-fiber (e a) (e-is-surjective (e a))  
                         ≈∎)
   
    lower-triangle : m ∘ lift-of-g ⇒ g
    lower-triangle b = as-equality-in-the-codomain 
                       (induced-map-on-the-truncated-fiber b (e-is-surjective b))
