{-# OPTIONS --safe --without-K #-}
module AoP.Kleene where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import AoP.Prelude
open import AoP.Relations
open import AoP.Joins using (⋃; inject; least)
open import AoP.Complement using (⊥)

-- Exercise 6.3. Start with no pairs and apply the recursion operator
-- repeatedly. Membership in the union records a finite stage at which
-- a pair appeared. Continuity allows one more application of Φ to pass
-- through this union; monotonicity alone proves the induction principle.
module Iterate {A B : Set} (Φ : (B ← A) → B ← A)
               (mono : ∀ R S → R ⊆ S → Φ R ⊆ Φ S) where
  stage : Nat → B ← A
  stage zero b a = ⊥
  stage (suc n) = Φ (stage n)

  ascending : ∀ n → stage n ⊆ stage (suc n)
  ascending zero ()
  ascending (suc n) = mono _ _ (ascending n)

  μ : B ← A
  μ = ⋃ stage

  induction : (X : B ← A) → Φ X ⊆ X → μ ⊆ X
  induction X closed = least stage X bounded
    where
    bounded : ∀ n → stage n ⊆ X
    bounded zero ()
    bounded (suc n) p = closed (mono (stage n) X (bounded n) p)

  unfold : μ ⊆ Φ μ
  unfold (zero , ())
  unfold (suc n , p) = mono (stage n) μ (inject stage n) p

  -- Only the forward inclusion of continuity is needed. The general
  -- hypothesis applies to any ascending chain, not just our stages.
  fold : (∀ (R : Nat → B ← A) → (∀ n → R n ⊆ R (suc n)) →
          Φ (⋃ R) ⊆ ⋃ (λ n → Φ (R n))) → Φ μ ⊆ μ
  fold continuous p with continuous stage ascending p
  ... | n , q = suc n , q
