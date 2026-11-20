{-# OPTIONS --safe --without-K #-}
module AoP.PrincipalMaximum where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Thinning using (Min)

-- Exercise 7.14. Transposing R at a gives the set of predecessors
-- of a. A maximum b of that set belongs to it, so b precedes a;
-- and since a belongs too, a precedes b. Conversely, either member
-- of a mutually comparable pair represents the same maximum.
module Law {A : Set} (R : A ← A) (rr : ∀ a → R a a)
           (trans : ∀ {a b c} → R a b → R b c → R a c) where
  MaxAt : A ← A
  MaxAt b a = Min (R ˘) b (λ x → R x a)

  compare : MaxAt ⊆ R ⊓ (R ˘)
  compare {b} {a} (ba , greatest) = ba , greatest a (rr a)

  maximum : R ⊓ (R ˘) ⊆ MaxAt
  maximum (ba , ab) = ba , λ x xa → trans xa ab
