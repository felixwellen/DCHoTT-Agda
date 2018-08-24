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
open import Flat
open import Im 

module Bosonic where

  {- 
    we will use ♭ as the bosonic modality
    bosonic types are the modal types for ♭
    coreduced types should be bosonic 
  -}

  _is-bosonic :
    ∀ (X :{♭} 𝒰₀) → 𝒰₀
  X is-bosonic = (♭-counit-at X) is-an-equivalence

  postulate
    coreduced-⇒-bosonic :
      ∀ {X :{♭} 𝒰₀} →
      (X is-coreduced) → X is-bosonic
    
     

  {- ... -}
