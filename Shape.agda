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
  open import PostulateAffineLine
  open import DiscreteTypes
  
  {- 

    assume that the discreteness given by 
    ♭ can be dectected by all maps from 𝔸 
    into some space being constant (chapter 8, [1])

    I added a user translation to my agda-input settings 
    for the shape symbol 'ʃ'. It is not '\int', but the 
    'esh' symbol (the IPA sign for 'sh').
  -}


  private
    data #ʃ (A : 𝒰₀) : 𝒰₀ where
      #σ : A → #ʃ A
      #κ  : (𝔸 → #ʃ A) → #ʃ A
      #κ′ : (𝔸 → #ʃ A) → #ʃ A
      
  ʃ : (A : 𝒰₀) → 𝒰₀
  ʃ A = #ʃ A
  
  module _ {A : 𝒰₀} where
    σ : A → ʃ A
    σ A = #σ A
  
    κ : (𝔸 → ʃ A) → ʃ A
    κ = #κ
  
    κ′ : (𝔸 → ʃ A) → ʃ A
    κ′ = #κ′
    
    postulate
      p1 : (γ : 𝔸 → ʃ A) → ((x : 𝔸) → γ x ≈ κ γ)
      p2 : (x : ʃ A) → x ≈ κ′ (const x)


    module _ (B : 𝒰₀) where
      ʃ-as-HIT-recursion :
        (A → B) 
        → (κB : (𝔸 → B) → B)
        → (κ′B : (𝔸 → B) → B)
        → ((γ : 𝔸 → B) → ((x : 𝔸) → γ x ≈ κB γ))
        → ((x : B) → x ≈ κ′B (const x))
        → (ʃ A → B)
      ʃ-as-HIT-recursion σB _  _   _  _  (#σ a)  = σB a
      ʃ-as-HIT-recursion σB κB κ′B p1 p2 (#κ γ)  = κB (λ (x : 𝔸) → ʃ-as-HIT-recursion σB κB κ′B p1 p2 (γ x))
      ʃ-as-HIT-recursion σB κB κ′B p1 p2 (#κ′ γ) = κ′B ((λ (x : 𝔸) → ʃ-as-HIT-recursion σB κB κ′B p1 p2 (γ x)))
      postulate
        uniqueness-of-ʃ-recursion-1 :
           (σB : A → B) 
          → (κB : (𝔸 → B) → B)
          → (κ′B : (𝔸 → B) → B)
          → (p1B : (γ : 𝔸 → B) → ((x : 𝔸) → γ x ≈ κB γ))
          → (p2B : (x : B) → x ≈ κ′B (const x))
          → (γ : 𝔸 → ʃ A) → (x : 𝔸)
          → (ʃ-as-HIT-recursion σB κB κ′B p1B p2B) ⁎ (p1 γ x) ≈ p1B ((ʃ-as-HIT-recursion σB κB κ′B p1B p2B) ∘ γ) x
            
    module _ (P : ʃ A → 𝒰₀) where
      ʃ-as-HIT-induction :
        ((x : A) → (P (σ x)))
        → (κP : (γ : 𝔸 → ʃ A) → (p : (x : 𝔸) → P (γ x)) → P (κ γ))
        → ((γ : 𝔸 → ʃ A) → (x : 𝔸) → (p : (x : 𝔸) → P (γ x)) → transport P (p1 γ x) (p x) ≈ κP γ p)
        → (κ′P : (γ : 𝔸 → ʃ A) → (p′ : (x : 𝔸) → P (γ x)) → P (κ′ γ))   
        → ((x : ʃ A) → (pₓ : P x) → transport P (p2 x) pₓ ≈ κ′P (const x) (const pₓ))
        → ((x : ʃ A) → P x)
      ʃ-as-HIT-induction pσ _   _   _    _   (#σ x) = pσ x
      ʃ-as-HIT-induction pσ pκP pp1 pκ′P pp2 (#κ γ) = pκP γ (λ (x : 𝔸) → ʃ-as-HIT-induction pσ pκP pp1 pκ′P pp2 (γ x))
      ʃ-as-HIT-induction pσ pκP pp1 pκ′P pp2 (#κ′ γ) = pκ′P γ (λ (x : 𝔸) → ʃ-as-HIT-induction pσ pκP pp1 pκ′P pp2 (γ x))

       
  {- 
    Now, it is about showing the properties of ʃ,
    we are really interested in:
    It is a modality reflecting into the discrete types.
  -}
  
  ʃ-_is-discrete : (A : 𝒰₀) → (ʃ A) is-discrete
  ʃ- A is-discrete =
    has-left-inverse κ′ by (λ (x : ʃ A) → p2 x ⁻¹)
    and-right-inverse κ by (λ (γ : 𝔸 → ʃ A) → fun-ext (p1 γ))


  module _ {A : 𝒰₀} where
    {-
       induction for the shape modality
    -}

    ʃ-induction :
      ∀ (P : ʃ A → 𝒰₀)
      → ((x : ʃ A) → (P x) is-discrete)
      → ((x : A) → P(σ x))
      → ((x : ʃ A) → P x)
    ʃ-induction P P-is-discrete base-case =
      ʃ-as-HIT-induction
        P
        base-case
        (λ γ pκ → transport P (p1 γ origin-of-𝔸) (pκ origin-of-𝔸))
        (λ γ x₁ p →
          conclude-equality-of-values-from-discreteness
            (P-is-discrete (κ γ)) _  x₁ origin-of-𝔸)
        (λ γ pκ′ → transport P
                             ( γ origin-of-𝔸
                              ≈⟨ p1 γ origin-of-𝔸 ⟩
                               κ γ
                              ≈⟨ p2 (κ γ) ⟩
                               κ′ (const (κ γ))
                              ≈⟨ (κ′ ⁎ (fun-ext (p1 γ))) ⁻¹ ⟩ 
                               κ′ γ
                              ≈∎)
                             (pκ′ origin-of-𝔸))
        (λ x pₓ →  {!!}) 

  

