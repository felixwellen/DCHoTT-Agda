{-# OPTIONS --without-K #-}

module Univalence where 

open import Basics public
open import EqualityAndPaths public
open import Equivalences public

-- univalence
-- according to Ex. 4.6 the following axiom might be inconsistent... 
-- I do not know, if this really is the case, because I am fixing the quasiinverse
-- NO -- seems to be ok: in the exercise, ≃ is replaced by a version, where 
--       equivalences are not so merely
postulate 
  ua : ∀ {i} {A B : U i} → A ≃ B → A ≈ B
  ua-is-an-equivalence : ∀ {i} {A B : U i} → (ua {i} {A} {B}) is-quasiinverse-of U-transport

-- ua ∘ U-transport ∼ id {A≈B} and U-transport ∘ ua ∼ id {A≃B}


