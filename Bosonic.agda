{- 

  Trying to solve the problem from this email excerpt (of Urs): 


So consider the full system of modalities for "super-differential
cohesion" or "solid cohesion", for short, as stated here:

 https://ncatlab.org/nlab/show/geometry+of+physics+--+categories+and+toposes#ProgressionOfModalitiesOnSolidTopos

Moreover, consider this with the extra condition of "left Aufhebung"
at the third stage, meaning that not only

 Rh > Im

but also

 rightsquigarrow > Im

 (read: co-reduced types are bosonic)

which is verified in the model of SuperFormalSmoothSets, as shown here:

 https://ncatlab.org/nlab/show/geometry+of+physics+--+supergeometry#ProgressionOfIdempotentEndofunctors

Then the following Proposition should be provable:

_For V any homogeneous type (as in Felix's Def. 4.8 of
https://arxiv.org/abs/1806.05966) and X any V-manifold, we have that
\rightsquigarrow(X) is a \rightsquigarrow(V)-manifold._

In words this means: Underlying any supermanifold is an ordinary manifold.

This follows immediately from the following Lemma:

_If a function f is formally etale, then so is \rightsquigarrow(f)_.

The idea of the proof of this Lemma is that \rightsquigarrow, being a
right adjoint, preserves the pullback square that witnesses formally
etale-ness, and due to the Aufhebung-relations, the resulting pullback
square exhibits formally etale-ness of \rightsquigarrow(f).

When I prove this as here

https://ncatlab.org/nlab/show/geometry+of+physics+--+supergeometry#BosonicModalityPreservesLocalDiffeomorphism

I use

1. a Yoneda argument to deduce

   Im(X) \simeq Im( \rightsquigarrow(X) )

from

  \rightrightarrows( \Re(X) ) \simeq \Re( X )

  which holds by assumption

2. \rightsquigarrow takes the unit of Im on X to the unit of Im on
\rightsquigarrow X.

  which is evident in the model of SuperFormalSmoothSets. I suspect
this follows abstractly, but I haven't really checked this yet...

So these two steps may need more thinking for making them more formal.

But it shouldn't be too intricate, I suppose, and the resulting
Proposition will be of interest!


-}

open import Basics
open import Equivalences
open import Flat renaming
  (♭ to ⇝;
   ♭-counit to ⇝-counit;
   ♭-counit-at to ⇝-counit-at;
   ♭→ to ⇝→;
   ♭-recursion to ⇝-recursion)  -- \r~
-- open import Im
open import EtaleMaps

module Bosonic where

  {- 
    we will use ⇝ as the bosonic modality
    bosonic types are the modal types for ⇝
    coreduced types should be bosonic 
  -}

  _is-bosonic :
    ∀ (X :{♭} 𝒰₀) → 𝒰₀
  X is-bosonic = (⇝-counit-at X) is-an-equivalence

  postulate
    coreduced-⇒-bosonic :
      ∀ {X :{♭} 𝒰₀} →
      (X is-coreduced) → X is-bosonic

  {-
    This should yield a natural morphism ⇝ℑX ─≃→ ℑ⇝X
  -}

  ⇝-preserves-coreduced : ∀ {X :{♭} 𝒰₀}
    → ⇝ (ℑ X) ≃ ℑ X
  ⇝-preserves-coreduced {X} =
    ⇝-counit-at (ℑ X)
      is-an-equivalence-because
        coreduced-⇒-bosonic (ℑ-is-coreduced X)

  ⇝-ℑ-compare :
    ∀ {X :{♭} 𝒰₀}
    → ℑ (⇝ X) → ⇝ (ℑ X) 
  ⇝-ℑ-compare {X} =
    ⇝-recursion
      (ℑ→ (⇝-counit-at X))
      (coreduced-⇒-bosonic (ℑ-is-coreduced (⇝ X)))

  ⇝-ℑ-commute :
    ∀ {X :{♭} 𝒰₀}
    → ⇝-ℑ-compare {X} is-an-equivalence
  ⇝-ℑ-commute {X} =
    let
      φ : ℑ X → ⇝ (ℑ X)
      φ = left-inverse-of ⇝-counit given-by coreduced-⇒-bosonic (ℑ-is-coreduced _)
      ψ : ℑ (⇝ X) → ℑ X
      ψ = ℑ→ ⇝-counit
    in has-left-inverse {!!} by {!!}
       and-right-inverse {!!} by {!!}
  
  {- ... -}

  module bosonification-of-formally-étale-maps {X Y : 𝒰₀} (f : X → Y) where
    -- (f-is-étale : f is-étale) where

    {-

    the overall goal is to show, that the bosonification(?) of a 
    formally étale map is formally étale, which amount to the 
    following:

    for any f : X → Y, applying ⇝ preserves pb
    
      X ──→ ℑX       ⇝X ──→ ⇝ℑX ─≃→ ℑ⇝X
      |      |        |               |
      |  pb  |    ⇒   |      pb       |
      ↓      ↓        ↓               ↓ 
      Y ──→ ℑY       ⇝Y ──→ ⇝ℑY ─≃→ ℑ⇝Y

    and 

    that the vertical maps of the right square are the ℑ-units
    at ⇝X and ⇝Y.

    -}

    

  

  {- ... -}
