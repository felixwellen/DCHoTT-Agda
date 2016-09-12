{-# OPTIONS --without-K #-}

module PullbackPasting where 
  open import Basics
  open import EqualityAndPaths
  open import Equivalences
  open import HalfAdjointEquivalences
  open import Homotopies
  open import FunctionExtensionality
  open import Language
  open import Pullback

  -- pasting

  --          p₁
  --   P₂-> P₁-> A
  --   |    |    |
  --   |    p₂   f
  --   |    |    |
  --   v    v g  v
  --   D -> B -> C

  module proof-of-pullback-lemma (A B C D : U₀)(f : A → C)(g : B → C)(h : D → B) where
    -- prove the iterated cone type is equivalent to the cone type of the outer pullback
      open pullback-uniqueness using (cone-to-map)
      inner-cone-to-outer-cone : ∀ {Z : U₀} 
        → cone Z (p₂-of-pullback f g) h → cone Z f (g ∘ h)
        -- Z ─z₁→ P₁ ─p₁→ A
        -- |      |
        -- z₂ ⇙γ  p₂
        -- ↓      ↓
        -- D ─h─→ B
      inner-cone-to-outer-cone (z₁ and z₂ commute-by γ) = 
                              p₁ ∘ z₁ and z₂ commute-by (λ z → p-homotopy (z₁ z) • g ⁎ γ z)

      outer-cone-to-inner-cone : ∀ (Z : U₀)
        → cone Z f (g ∘ h) → cone {pullback f g} {_} {_}  Z p₂ h
        -- Z ─────z₁────→ A
        -- |              |
        -- z₂     ⇙γ      f
        -- ↓              ↓
        -- D ─h─→ B ──g─→ C
      outer-cone-to-inner-cone Z (z₁ and z₂ commute-by γ) = 
        let ψ : Z → pullback f g
            ψ = cone-to-map (z₁ and (h ∘ z₂) commute-by γ)
        in ψ and z₂ commute-by (λ z → refl)


      -- rectify a Z-cone over the inner pullback
      -- Z ─z₁→ P₁ ─p₁→ A
      -- |      |       |
      -- z₂ ⇙γ  p₂      f
      -- ↓      ↓       ↓
      -- D ─h─→ B ──g─→ C
      module rectify (Z : U₀)(z₁ : Z → pullback f g)(z₂ : Z → D)(γ : p₂ ∘ z₁ ∼ h ∘ z₂) where
         -- given a cone, construct a map Z → P₁ homotopic to z₁ such that
         -- the new cone commutes strictly

         -- introduce shorthand notation for terms in the pullback
         p_,_,_ : ∀ (a : A)(b : B)(η : f(a) ≈ g(b)) → pullback f g
         p a , b , η = a and b are-in-the-same-fiber-by η

         the-map′ : Z → pullback f g
         the-map′ z = p₁ (z₁ z) and h (z₂ z) are-in-the-same-fiber-by p-homotopy (z₁ z) • g ⁎ γ z

         equality : ∀ (a : A)(b : B)(η : f(a) ≈ g(b)) 
                    → (b′ : B) → (ζ : b ≈ b′)
                    → (p a , b′ , η • g ⁎ ζ) ≈ (p a , b , η)
         equality a b η .b refl =
                    let equal-path :  η • g ⁎ refl ≈  η 
                        equal-path = refl-is-right-neutral η ⁻¹
                    in (λ δ → p a , b , δ) ⁎ equal-path
                                     
         mapping-to-the-codomain-has-trivial-application : 
           ∀ {a : A} {b : B} (γ γ′ : f(a) ≈ g(b)) 
           → (ζ : γ ≈ γ′) 
           → (λ (η : f(a) ≈ g(b)) → b) ⁎ ζ ≈ refl
         mapping-to-the-codomain-has-trivial-application γ .γ refl = refl
                                                  
         compute-projection : ∀ {a : A} {b : B} (η : f(a) ≈ g(b)) 
                              → (b′ : B) → (ζ : b ≈ b′)
                              → p₂ ⁎ (equality a b η b′ ζ) ≈ ζ ⁻¹
         compute-projection η _ refl = application-commutes-with-composition _ p₂
                                       (refl-is-right-neutral η ⁻¹)
                                         • (application-commutes-with-inversion _ (refl-is-right-neutral η) •
                                           invert-both-sides (mapping-to-the-codomain-has-trivial-application η (η • refl)
                                                             (refl-is-right-neutral η)))

         project-uniqueness : ∀ (x : pullback f g)
                              →  refl ≈ p₂ ⁎ uniqueness-for-pullbacks x
         project-uniqueness (a and b are-in-the-same-fiber-by η) = refl
                 
         z₁-equals-the-map : (z : Z) → the-map′ z ≈ z₁ z 
         z₁-equals-the-map z = equality _ _ _ (h (z₂ z)) (γ z) • uniqueness-for-pullbacks (z₁ z)

         compute-projection-further : ∀ (z : Z) → p₂ ⁎ z₁-equals-the-map z ≈ γ z ⁻¹
         compute-projection-further z = 
           let bla : 
                   z₁-equals-the-map z • uniqueness-for-pullbacks (z₁ z) ⁻¹ 
                     ≈ equality (p₁ (z₁ z)) (p₂ (z₁ z)) (p-homotopy (z₁ z)) (h (z₂ z)) (γ z) 
               bla = move-down-right _ _ _ refl
           in
             refl-is-right-neutral _ •
               (λ η → p₂ ⁎ z₁-equals-the-map z • η ⁻¹) ⁎ project-uniqueness (z₁ z)
                      • (λ η → p₂ ⁎  z₁-equals-the-map z • η) ⁎
                           (application-commutes-with-inversion p₂ (uniqueness-for-pullbacks (z₁ z))) ⁻¹ 
                      • application-commutes-with-concatenation p₂ (z₁-equals-the-map z)
                      (uniqueness-for-pullbacks (z₁ z) ⁻¹)
                      ⁻¹ • ((λ x → p₂ ⁎ x) ⁎ bla) • compute-projection (p-homotopy (z₁ z)) (h (z₂ z)) (γ z)

         -- every inner cone is equal to a cone with trivial 2-cell -- the rectified cone
         rectified-inner-cone : cone Z (p₂-of-pullback f g) h
                                -- Z ─z₁→ P₁ ─p₁→ A
                                -- |      |       |
                                -- z₂ ⇙γ  p₂      f
                                -- ↓      ↓       ↓
                                -- D ─h─→ B ──g─→ C
         rectified-inner-cone =
                              let z₁′ :  Z → pullback f g
                                  z₁′ = the-map′ 
                              in z₁′ and z₂ commute-by (λ z → refl)

         z₁-deformed-cone-is-equal :
           ∀ (z₁′ : Z → pullback f g) (η : z₁′ ≈ z₁)
             → in-the-type (cone Z p₂ h) we-have-an-equality
               (z₁′ and z₂ commute-by (λ z → p₂ ⁎ ((equality-to-homotopy η) z) • (γ z))) ≈ (z₁ and z₂ commute-by γ)
         z₁-deformed-cone-is-equal .z₁ refl = (λ H → z₁ and z₂ commute-by H) ⁎ refl
                                                                               
         equality-of-the-cones : rectified-inner-cone ≈ (z₁ and z₂ commute-by γ)
         equality-of-the-cones =
           let the-path-is-inverse-to-γ :
                 ∀ (z : Z)
                 → γ z ⁻¹ ≈ p₂ ⁎ equality-to-homotopy (fun-ext z₁-equals-the-map) z
               the-path-is-inverse-to-γ z =
                 compute-projection-further z ⁻¹
                  • (λ x → p₂ ⁎ x) ⁎ cancel-fun-ext z₁-equals-the-map z ⁻¹
           in (λ γ′ → the-map′ and z₂ commute-by γ′) ⁎
                      fun-ext (λ z → ⁻¹-is-left-inversion (γ z) ⁻¹
                        • (λ γ′ → γ′ • γ z) ⁎ the-path-is-inverse-to-γ z)
                        • z₁-deformed-cone-is-equal the-map′ (fun-ext z₁-equals-the-map)

      -- end of rectification

      -- factor an outer cone into smaller 2-cells (i.e. into γ and two identity 2-cells from the universal property of pullback f g)
                                -- Z ─────z₁──────\
                                ---| .            |
                                ---|  ψ .         ↓
                                -- |      P₁ ─p₁→ A
                                -- |      |       |
                                -- z₂     p₂      f    ⇙γ
                                -- ↓      ↓       ↓
                                -- D ─h─→ B ──g─→ C
      module factor (Z : U₀) (z₁ : Z → A) (z₂ : Z → D) (γ : f ∘ z₁ ∼ (g ∘ h) ∘ z₂) where
             induced-map : Z → pullback f g
             induced-map = cone-to-map {_} {_} {_} {f} {g} {_} (z₁ and (h ∘ z₂) commute-by γ)
             ψ = induced-map
             
             recompose-cone : in-the-type (cone Z f (g ∘ h)) we-have-an-equality
                   (z₁ and z₂ commute-by γ)
                 ≈ (p₁ ∘ ψ
                       and z₂ commute-by
                       (λ z → p-homotopy (ψ z) • refl {a = g (h (z₂ z))}))
             recompose-cone = let refl-doesnt-matter : (z : Z) → γ z ≈ p-homotopy (ψ z) • refl {a = g (h (z₂ z))}
                                  refl-doesnt-matter z = refl-is-right-neutral (γ z)
                              in (λ η → z₁ and z₂ commute-by η) ⁎ fun-ext refl-doesnt-matter
             
      invers-left : ∀ (Z : U₀) (c : cone {pullback f g} {_} {_}  Z p₂ h)
                → outer-cone-to-inner-cone Z (inner-cone-to-outer-cone c) ≈ c
      invers-left Z (z₁ and z₂ commute-by γ) = rectify.equality-of-the-cones Z z₁ z₂ γ

      invers-right : ∀ (Z : U₀) (c : cone Z f (g ∘ h))
                → c ≈ inner-cone-to-outer-cone (outer-cone-to-inner-cone Z c)
      invers-right Z (z₁ and z₂ commute-by γ) = factor.recompose-cone Z z₁ z₂ γ


                                  -- P₂─p₁→ P₁ ─p₁→ A
                                  -- |      |       |
                                  -- p₂ ⇙γ  p₂      f
                                  -- ↓      ↓       ↓
                                  -- D ─h─→ B ──g─→ C

      proof-of-equivalence : 
        ∀ {Z : U₀} → inner-cone-to-outer-cone {Z} is-an-equivalence
      proof-of-equivalence {Z} =
        has-left-inverse
          (outer-cone-to-inner-cone Z) by (invers-left Z)
        and-right-inverse
          (outer-cone-to-inner-cone Z) by (invers-right Z)
                            
      pasting-lemma-on-cone-spaces : 
        ∀ {Z : U₀} → cone Z (p₂-of-pullback f g) h ≃ cone Z f (g ∘ h) 
      pasting-lemma-on-cone-spaces = 
        inner-cone-to-outer-cone is-an-equivalence-because proof-of-equivalence

      extend-inner-cone :
        ∀ {Z Z′ : U₀} (φ : Z′ → Z)
        → cone {pullback f g} {_} {_} Z p₂ h → cone {pullback f g} {_} {_} Z′ p₂ h
      extend-inner-cone φ (z₁ and z₂ commute-by γ) = 
        z₁ ∘ φ and z₂ ∘ φ commute-by (λ z → γ (φ z))

      extend-outer-cone :
        ∀ {Z Z′ : U₀} (φ : Z′ → Z)
        → cone Z f (g ∘ h) → cone Z′ f (g ∘ h)
      extend-outer-cone φ (z₁ and z₂ commute-by γ) = 
        z₁ ∘ φ and z₂ ∘ φ commute-by (λ z → γ (φ z))

      -- naturality is a part of the result
      naturality-of-inner-cone-to-outer-cone :
        ∀ {Z Z′ : U₀} (φ : Z → Z′)
        → inner-cone-to-outer-cone ∘ extend-inner-cone φ ∼ extend-outer-cone φ ∘ inner-cone-to-outer-cone
      naturality-of-inner-cone-to-outer-cone φ (z₁ and z₂ commute-by γ) = refl

      

      -- (Z → PB f g∘h) ≃ (cone Z f g∘h) ≃ (cone Z p₂ h) ≃ (Z → PB p₂ h)

      pasting-lemma-on-mapping-spaces : 
        ∀ {Z : U₀}
        → (Z → pullback (p₂-of-pullback f g) h) ≃ (Z → pullback f (g ∘ h))
      pasting-lemma-on-mapping-spaces = 
        (pullback-is-universal  ∘≃ pasting-lemma-on-cone-spaces) ∘≃ pullback-is-universal ⁻¹≃

      inner-map-to-outer-map :  
        ∀ {Z : U₀}
        → (Z → pullback (p₂-of-pullback f g) h) → (Z → pullback f (g ∘ h))
      inner-map-to-outer-map = underlying-map-of pasting-lemma-on-mapping-spaces

      naturality-on-mapping-spaces : 
        ∀ {Z Z′ : U₀} (φ : Z → Z′)
        → inner-map-to-outer-map ∘ (λ ξ → ξ ∘ φ) ∼ (λ ξ → ξ ∘ φ) ∘ inner-map-to-outer-map
      naturality-on-mapping-spaces φ ξ = refl
      

      -- as equivalence of the two pullbacks
      pasting-lemma : pullback (p₂-of-pullback f g) h ≃ pullback f (g ∘ h)
      pasting-lemma = 
                    representability (pullback f (g ∘ h)) ∘≃
                       pasting-lemma-on-mapping-spaces ∘≃
                         representability (pullback (p₂-of-pullback f g) h) ⁻¹≃

      equivalence-of-the-pullbacks : pullback (p₂-of-pullback f g) h → pullback f (g ∘ h)
      equivalence-of-the-pullbacks = underlying-map-of pasting-lemma

      

      -- compatibility with induced maps

      -- we show: equivalence of pullbacks factors induced maps

                                  -- Z-z₁---\
                                  -- |      v
                                  -- z₂     P₁ ─p₁→ A
                                  -- |      |       |
                                  -- |      p₂      f    ⇙γ
                                  -- v      ↓       ↓
                                  -- D ─h─→ B ──g─→ C
      module factor-induced-maps (Z : U₀) (z₁ : Z → pullback f g) (z₂ : Z → D) (γ : p₂ ∘ z₁ ∼ h ∘ z₂) where
        induced-map : Z → pullback (p₂-of-pullback f g) h
        induced-map = induced-map-to-pullback z₁ z₂ γ
      
        induced-map′ : Z → pullback f (g ∘ h)
        induced-map′ = induced-map-to-pullback (p₁ ∘ z₁) z₂ (λ z → p-homotopy (z₁ z) • g ⁎ γ z) 

        -- need to show:
        e = underlying-map-of pasting-lemma
        e⁻¹ = underlying-map-of (pasting-lemma ⁻¹≃)
        e⁻¹∘e∼1 = unit-of-the-equivalence pasting-lemma
        induced-maps-factor : e ∘ induced-map ∼ induced-map′
        induced-maps-factor z = refl

        induced-maps-factor′ : induced-map ∼ e⁻¹ ∘ induced-map′
        induced-maps-factor′ z = e⁻¹∘e∼1 (induced-map z) ⁻¹ • e⁻¹ ⁎ induced-maps-factor z


  pasting-lemma : ∀ {A B C D : U₀} (f : A → C) (g : B → C) (h : D → B)
                  → pullback (p₂-of-pullback f g) h ≃ pullback f (g ∘ h)
  pasting-lemma f g h = proof-of-pullback-lemma.pasting-lemma _ _ _ _ f g h

  

