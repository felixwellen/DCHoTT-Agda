{-# OPTIONS --without-K #-}


{-
  An attempt to write down the shape functor from Mike Shulman's
  real cohesion paper 
  (chapter 9, https://arxiv.org/abs/1509.07584 [1]).
-}

module Shape where
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Equivalences
  open import FunctionExtensionality
  open import Flat renaming (_is-discrete to _is-crisply-discrete)

  const : {X Y : 𝒰₀} → Y → (X → Y)
  const y₀ = λ _ → y₀
  
  {- 

    assume that the discreteness given by 
    ♭ can be dectected by all maps from 𝔸 
    into some space being constant (chapter 8, [1])
  -}

  postulate
    𝔸 : 𝒰
    𝔸-nullfies-discrete-types :
      ∀ (A :{♭} 𝒰₀)
      → A is-crisply-discrete ≃ const {𝔸} {A} is-an-equivalence

  _is-discrete : ∀ (A : 𝒰₀) → 𝒰₀
  A is-discrete = const {𝔸} {A} is-an-equivalence

  private
    data #∫ (A : 𝒰₀) : 𝒰₀ where
      #σ : A → #∫ A
      #κ  : (𝔸 → #∫ A) → #∫ A
      #κ′ : (𝔸 → #∫ A) → #∫ A
      
  ∫ : (A : 𝒰₀) → 𝒰₀
  ∫ A = #∫ A
  
  module _ {A : 𝒰₀} where
    σ : A → ∫ A
    σ A = #σ A
  
    κ : (𝔸 → ∫ A) → ∫ A
    κ = #κ
  
    κ′ : (𝔸 → ∫ A) → ∫ A
    κ′ = #κ′
    
    postulate
      p1 : (γ : 𝔸 → ∫ A) → ((x : 𝔸) → γ x ≈ κ γ)
      p2 : (x : ∫ A) → x ≈ κ′ (const x)


    module _ (B : 𝒰₀) where
      ∫-as-HIT-recursion :
        (A → B) 
        → (κB : (𝔸 → B) → B)
        → (κ′B : (𝔸 → B) → B)
        → ((γ : 𝔸 → B) → ((x : 𝔸) → γ x ≈ κB γ))
        → ((x : B) → x ≈ κ′B (const x))
        → (∫ A → B)
      ∫-as-HIT-recursion σB _  _   _  _  (#σ a)  = σB a
      ∫-as-HIT-recursion σB κB κ′B p1 p2 (#κ γ)  = κB (λ (x : 𝔸) → ∫-as-HIT-recursion σB κB κ′B p1 p2 (γ x))
      ∫-as-HIT-recursion σB κB κ′B p1 p2 (#κ′ γ) = κ′B ((λ (x : 𝔸) → ∫-as-HIT-recursion σB κB κ′B p1 p2 (γ x)))
      postulate
        uniqueness-of-∫-recursion-1 :
           (σB : A → B) 
          → (κB : (𝔸 → B) → B)
          → (κ′B : (𝔸 → B) → B)
          → (p1B : (γ : 𝔸 → B) → ((x : 𝔸) → γ x ≈ κB γ))
          → (p2B : (x : B) → x ≈ κ′B (const x))
          → (γ : 𝔸 → ∫ A) → (x : 𝔸)
          → (∫-as-HIT-recursion σB κB κ′B p1B p2B) ⁎ (p1 γ x) ≈ p1B ((∫-as-HIT-recursion σB κB κ′B p1B p2B) ∘ γ) x
            
    module _ (P : ∫ A → 𝒰₀) where
      ∫-as-HIT-induction :
        ((x : A) → (P (σ x)))
        → (κP : (γ : 𝔸 → ∫ A) → (p : (x : 𝔸) → P (γ x)) → P (κ γ))
        → ((γ : 𝔸 → ∫ A) → (x : 𝔸) → (p : (x : 𝔸) → P (γ x)) → transport P (p1 γ x) (p x) ≈ κP γ p)
        → (κ′P : (γ : 𝔸 → ∫ A) → (p′ : (x : 𝔸) → P (γ x)) → P (κ′ γ))   
        → ((x : ∫ A) → (pₓ : P x) → transport P (p2 x) pₓ ≈ κ′P (const x) (const pₓ))
        → ((x : ∫ A) → P x)
      ∫-as-HIT-induction pσ _   _   _    _   (#σ x) = pσ x
      ∫-as-HIT-induction pσ pκP pp1 pκ′P pp2 (#κ γ) = pκP γ (λ (x : 𝔸) → ∫-as-HIT-induction pσ pκP pp1 pκ′P pp2 (γ x))
      ∫-as-HIT-induction pσ pκP pp1 pκ′P pp2 (#κ′ γ) = pκ′P γ (λ (x : 𝔸) → ∫-as-HIT-induction pσ pκP pp1 pκ′P pp2 (γ x))

       
  {- 
    Now, it is about showing the properties of ∫,
    we are really interested in:
    It is a modality reflecting into the discrete types.
  -}
  
  ∫-_is-discrete : (A : 𝒰₀) → (∫ A) is-discrete
  ∫- A is-discrete =
    has-left-inverse κ′ by (λ (x : ∫ A) → p2 x ⁻¹)
    and-right-inverse κ by (λ (γ : 𝔸 → ∫ A) → fun-ext (p1 γ))

  {- 
      describe κ 
  -}

  paths-are-constant-in-∫- : 
    ∀ (A : 𝒰₀) (γ : 𝔸 → ∫ A)
    → γ ⇒ const (κ γ)
  paths-are-constant-in-∫- _ γ = p1 γ

  module _ {A : 𝒰₀} where
    {-
       induction for the shape modality
    -}
{-    
    ∫-induction :
      ∀ (P : ∫ A → 𝒰₀)
      → ((x : ∫ A) → (P x) is-discrete)
      → ((x : A) → P(σ x))
      → ((x : ∫ A) → P x)
    ∫-induction P P-is-discrete base-case x =
      ∫-as-HIT-induction
        P
        base-case
        (λ γ p → {!!}) {!!} {!!} {!!} {!!}
-}  
  

