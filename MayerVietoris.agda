{-# OPTIONS --without-K #-}
  
module MayerVietoris where 
  open import Basics
  open import EqualityAndPaths
  open import Homotopies
  open import Equivalences
  open import Pullback
  open import PullbackSquare
  open import Language
  open import InfinityGroups

  -- mayer vietoris in ∞-categories:


  -- from nlab page on mayer vietoris
  -- https://ncatlab.org/nlab/show/Mayer-Vietoris+sequence
  --
  -- X ×B Y -→ X        X ×B Y -→ B
  --   |  ⌟    |          |  ⌟    |
  --   |       f   ⇦⇒     |       Δ
  --   ↓       ↓          ↓       ↓
  --   Y -g--→ B        X × Y → B × B
  -- just show: the right square is a pullback
  module proof-of-mayer-vietoris-part-1 (X Y B : U₀) (f : X → B) (g : Y → B) where
    lemma-1 : ∀ (fx gy : B) (γ : fx ≈ gy) 
              → γ ≈ π₁ ⁎ ×-create-equality (refl { a = fx }) γ ⁻¹ • π₂ ⁎ ×-create-equality (refl { a = fx }) γ
    lemma-1 fx .fx refl = refl

    map-to-pullback : pullback Δ (f ×→ g) → pullback f g
    map-to-pullback (b and (x , y) are-in-the-same-fiber-by γ) =
                       x and y are-in-the-same-fiber-by (π₁ ⁎ γ) ⁻¹ • π₂ ⁎ γ

    map-from-pullback : pullback f g → pullback Δ (f ×→ g)
    map-from-pullback (x and y are-in-the-same-fiber-by γ) =
                      f(x) and (x , y) are-in-the-same-fiber-by (×-create-equality refl γ)

    calculation : ∀ (b₁ b₂ b₃ b₄ : B) (γ : b₂ ≈ b₁) (η₁ : b₂ ≈ b₃) (η₂ : b₂ ≈ b₄) 
                  → Δ ⁎ γ ⁻¹ • (×-create-equality η₁ η₂) ≈ ×-create-equality (γ ⁻¹ • η₁) (γ ⁻¹ • η₂)
    calculation b₁ .b₁ _ _ refl η₁ η₂ = refl

    triviality : ∀ (p1 p2 : B × B) (η : p1 ≈ p2)
                 → π₁ ⁎ ×-create-equality (π₁ ⁎ η) (π₂ ⁎ η) ≈ π₁ ⁎ η
    triviality p1 .p1 refl = refl

    lemma-2 : ∀ (b : B) (x : X) (y : Y) (γ : (b , b) ≈ (f x , g y))
              → Δ ⁎ (π₁ ⁎ ×-create-equality (π₁ ⁎ γ) (π₂ ⁎ γ)) ⁻¹ • 
                (×-create-equality (π₁ ⁎ γ) (π₂ ⁎ γ)) ≈ 
                ×-create-equality refl ((π₁ ⁎ γ) ⁻¹ • (π₂ ⁎ γ))
    lemma-2 b x y γ = (λ η → Δ ⁎ η ⁻¹ • ×-create-equality (π₁ ⁎ γ) (π₂ ⁎ γ)) ⁎ triviality _ _ γ • 
                      calculation _ _ _ _ (π₁ ⁎ γ) (π₁ ⁎ γ) (π₂ ⁎ γ) •
                      (λ η → ×-create-equality η (π₁ ⁎ γ ⁻¹ • π₂ ⁎ γ)) ⁎
                        ⁻¹-is-left-inversion (π₁ ⁎ γ) 

    left-inverse : ∀ (x : pullback Δ (f ×→ g))
                   → map-from-pullback (map-to-pullback x) ≈ x
    left-inverse (b and (x , y) are-in-the-same-fiber-by γ) = 
                 let b≈fx : b ≈ f(x)
                     b≈fx = π₁ ⁎ γ 
                     equality-transformation :  Δ ⁎ (π₁ ⁎ γ) ⁻¹ • γ
                                              ≈ ×-create-equality refl (π₁ ⁎ γ ⁻¹ • π₂ ⁎ γ)
                     equality-transformation =
                       (λ η → Δ ⁎ (π₁ ⁎ η) ⁻¹ • η) ⁎
                        (×-uniqueness-of-equality γ •
                       refl-is-right-neutral (×-create-equality (π₁ ⁎ γ) (π₂ ⁎ γ)) ⁻¹) •
                       lemma-2 b x y γ
                 in (equalitiy-action Δ (f ×→ g) b (f x) b≈fx (x , y) γ •
                       (λ η → _ and _ are-in-the-same-fiber-by η) ⁎ equality-transformation) ⁻¹

    right-inverse : ∀ (x : pullback f g)
                    → x ≈ map-to-pullback (map-from-pullback x)
    right-inverse (a and b are-in-the-same-fiber-by γ) =
                  (λ η → _ and _ are-in-the-same-fiber-by η) ⁎ lemma-1 (f a) (g b) γ

    map-from-pullback-is-an-equivalence :
      map-from-pullback is-an-equivalence
    map-from-pullback-is-an-equivalence =
      (has-left-inverse
        map-to-pullback by right-inverse ⁻¹∼
          and-right-inverse
        map-to-pullback by left-inverse ⁻¹∼)
    
    proof : pullback Δ (f ×→ g) ≃ pullback f g
    proof = map-to-pullback is-an-equivalence-because
      (has-left-inverse
        map-from-pullback by left-inverse
          and-right-inverse
        map-from-pullback by right-inverse)

                            

    {-
     show that 'map-from-pullback' is an induced map
     induced by:
     (x, y) -> f(x)
     (x, y, γ) -> (x,y) (forget)

          B
         /  \
        /    \
    X ×B Y--→(X × Y) ×B B
         \   /
          \ /
         X × Y
    -}

    ν : pullback f g → B
    ν (x and y are-in-the-same-fiber-by γ) = f(x)

    θ : pullback f g → X × Y
    θ (x and y are-in-the-same-fiber-by γ) = (x , y)

    ξ : Δ ∘ ν ∼ (f ×→ g) ∘ θ
    ξ (x and y are-in-the-same-fiber-by γ) = ×-create-equality refl γ

    induced-map : pullback f g → pullback Δ (f ×→ g)
    induced-map = induced-map-to-pullback ν θ ξ

    map-from-pullback∼induced-map : map-from-pullback ∼ induced-map
    map-from-pullback∼induced-map (a and b are-in-the-same-fiber-by γ) = refl

    induced-map-is-an-equivalence :
      induced-map is-an-equivalence
    induced-map-is-an-equivalence =
      equivalences-are-preserved-by-homotopy map-from-pullback
        induced-map map-from-pullback-is-an-equivalence map-from-pullback∼induced-map

    {-
    
      X ×B Y -ν-→ B
         | ⌟      |
         θ        Δ
         ↓        ↓
       X × Y -→ B × B
    -}

    as-pullback-square : pullback-square-with-right Δ bottom (f ×→ g) top ν left θ
    as-pullback-square =
      commutes-by ξ and-the-induced-map-is-an-equivalence-by induced-map-is-an-equivalence
    
  mayer-vietoris-part-1 : ∀ {X Y B : U₀} (f : X → B) (g : Y → B)
                          → pullback Δ (f ×→ g) ≃ pullback f g
  mayer-vietoris-part-1 f g = proof-of-mayer-vietoris-part-1.proof _ _ _ f g

  module lemma-on-pullbacks-of-Δ (BG : U₀) (e : BG) (D : U₀) (φ : D → Ω BG e) where
    open import CommonEquivalences

    -- strategy:
    -- first, calculate
    -- ΔG(g,h) = g • h⁻¹ = φ d
    -- <=> g = φ d • h
    -- where calculate means the construction of an
    -- equivalence between the pullbacks
    -- 'pullback ΔG φ' and 'pullback id φ×id'
    -- second step: pullback id φ×id = domain φ×id = D × G

    G = Ω BG e
    ΔG : G × G → G
    ΔG = ∞-group-Δ BG e

    φ•id : D × G → G
    φ•id (d , h) = φ d • h


    concatenate-h : ∀ (g h : G) (d : D)
                    → ( φ d ≈ g • h ⁻¹) ≃ (φ d • h ≈ g • h ⁻¹ • h)
    concatenate-h g h d = concatenate-right (φ d) (g • h ⁻¹) h
                          is-an-equivalence-because concatenating-is-an-equivalence (φ d) (g • h ⁻¹) h
    
    cancel-h-as-path : ∀ (g h : G)
      → g • h ⁻¹ • h ≈ g
    cancel-h-as-path g h = g • h ⁻¹ • h
                     ≈⟨ •-is-associative g (h ⁻¹) h ⁻¹ ⟩
                       g • (h ⁻¹ • h)
                     ≈⟨ (λ ξ → g • ξ) ⁎ ⁻¹-is-left-inversion h ⟩
                       g • refl
                     ≈⟨ refl-is-right-neutral g ⁻¹ ⟩
                       g
                     ≈∎
    cancel-h-as-path⁻¹ : ∀ (g h : G)
      → g ≈ g • h ⁻¹ • h 
    cancel-h-as-path⁻¹ g h = g
                     ≈⟨ refl-is-right-neutral g ⟩
                       g • refl
                     ≈⟨ (λ ξ → g • ξ) ⁎ ⁻¹-is-left-inversion h ⁻¹ ⟩
                       g • (h ⁻¹ • h)
                     ≈⟨ •-is-associative g (h ⁻¹) h ⟩
                       g • h ⁻¹ • h
                     ≈∎

    cancel-h : ∀ (g h : G) (d : D)
               → (φ d • h ≈ g • h ⁻¹ • h) ≃ (φ d • h ≈ g)
    cancel-h g h d = transport-as-equivalence id ((λ ξ →  φ d • h ≈ ξ) ⁎ (cancel-h-as-path g h))
    -- 'id' means transport from equality in the universe

    -- needed later to control 2-cells
    calc-inverse : ∀ (g : G) (d : D) → (γ : _)
      → cancel-h g g d ⁻¹≃ $≃ γ ≈ γ • cancel-h-as-path g g ⁻¹
    calc-inverse g d γ = (cancel-h g g d ⁻¹≃) $≃ γ 
                ≈⟨ equal-by-definition ⟩
                 (transport-as-equivalence id ((λ ξ → φ d • g ≈ ξ) ⁎ cancel-h-as-path g g ⁻¹)) $≃ γ 
                ≈⟨ (λ ξ → transport-as-equivalence id ξ $≃ γ) ⁎
                     application-commutes-with-inversion (λ ξ → φ d • g ≈ ξ) (cancel-h-as-path g g) ⁻¹ 
                 ⟩ 
                 transport-as-equivalence id ((λ ξ → φ d • g ≈ ξ) ⁎ (cancel-h-as-path g g ⁻¹)) $≃ γ 
                ≈⟨ compute-$≃-on-transports (cancel-h-as-path g g ⁻¹) γ ⟩
                 γ • cancel-h-as-path g g ⁻¹
                ≈∎

    solve-for-g : ∀ (g h : G) (d : D)
                  → (φ d ≈ g • h ⁻¹) ≃ (φ d • h ≈ g)
    solve-for-g g h d = (cancel-h g h d) ∘≃ (concatenate-h g h d)
    
    solve : pullback φ ΔG → pullback φ•id id  
    solve (d and (g , h) are-in-the-same-fiber-by γ) =
          (d , h) and g are-in-the-same-fiber-by solve-for-g g h d $≃ γ 

    solve⁻¹l : pullback φ•id id → pullback φ ΔG
    solve⁻¹l ((d , h) and g are-in-the-same-fiber-by γ) =
              d and (g , h) are-in-the-same-fiber-by left-inverse-applied-to-γ
             where left-inverse-applied-to-γ = left-inverse-of-the-equivalence
                                               (solve-for-g g h d) γ

    solve⁻¹r : pullback φ•id id → pullback φ ΔG 
    solve⁻¹r ((d , h) and g are-in-the-same-fiber-by γ) =
             d and (g , h) are-in-the-same-fiber-by right-inverse-applied-to-γ
             where right-inverse-applied-to-γ = right-inverse-of-the-equivalence
                                                (solve-for-g g h d) γ

    left-invertible : ∀ (x : pullback φ ΔG) → solve⁻¹l (solve x) ≈ x
    left-invertible (d and (g , h) are-in-the-same-fiber-by γ) =
                        (λ η → d and (g , h) are-in-the-same-fiber-by η) ⁎
                        unit-of-the-equivalence (solve-for-g g h d) γ

    right-invertible : ∀ (x : pullback φ•id id) → x ≈ solve (solve⁻¹r x) 
    right-invertible ((d , h) and g are-in-the-same-fiber-by γ) =
                         (λ η → (d , h) and g are-in-the-same-fiber-by η) ⁎
                        counit-of-the-equivalence (solve-for-g g h d) γ 

    solve-for-g-everywhere : pullback φ ΔG ≃ pullback φ•id id
    solve-for-g-everywhere = solve is-an-equivalence-because
                                   (has-left-inverse solve⁻¹l by left-invertible
                                    and-right-inverse solve⁻¹r by right-invertible)

    the-equivalence : pullback φ ΔG ≃ D × G
    the-equivalence = id-pullback-as-equivalence′ (D × G) G φ•id ∘≃ solve-for-g-everywhere

    as-map : D × G → pullback φ ΔG
    as-map (d , g) = solve⁻¹l ((d , g) and (φ d • g) are-in-the-same-fiber-by refl)

    as-map∼the-equivalence⁻¹ : as-map ∼ underlying-map-of (the-equivalence ⁻¹≃)
    as-map∼the-equivalence⁻¹ (d , g) = refl

    map-is-an-equivalence : as-map is-an-equivalence
    map-is-an-equivalence = the-map as-map is-an-equivalence-since-it-is-homotopic-to
                              underlying-map-of (the-equivalence ⁻¹≃) by as-map∼the-equivalence⁻¹
                              which-is-an-equivalence-by proof-of-equivalency (the-equivalence ⁻¹≃)

    {- now, as pullback square

     ∀ φ : D --> G
     D × G -ν-> D
       | ⌟      |
       θ        φ
       ↓        ↓
     G × G -ΔG→ G
    
     θ: (d,g) ↦ (φ(d),e)
     ν: (d,g) ↦ d
     φ ∘ ν ∼ ΔG ∘ θ

    -}

    ν : D × G → D
    ν (d , g) = d

    θ : D × G → G × G
    θ (d , g) = (φ(d) • g , g)

    φ∘ν∼ΔG∘θ :  φ ∘ ν ∼ ΔG ∘ θ
    φ∘ν∼ΔG∘θ (d , g) = left-inverse-of-the-equivalence
                       (solve-for-g (φ d • g) g d) refl

    induced-map : D × G → pullback φ ΔG
    induced-map = induced-map-to-pullback ν θ φ∘ν∼ΔG∘θ
    
    induced-map∼as-map : 
      induced-map ∼ as-map
    induced-map∼as-map (d , g) = refl

    as-pullback-square :
      pullback-square-with-right φ bottom ΔG top ν left θ
    as-pullback-square = commutes-by φ∘ν∼ΔG∘θ 
                         and-the-induced-map-is-an-equivalence-by
                         (the-map induced-map is-an-equivalence-since-it-is-homotopic-to
                            as-map by induced-map∼as-map which-is-an-equivalence-by
                            map-is-an-equivalence)
