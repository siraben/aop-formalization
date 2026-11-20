{-# OPTIONS --safe --without-K #-}
module AoP.NegationLaws where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Complement using (⊥; ¬_; _⊔_; module DeMorgan)
open import AoP.Polynomial using (inl; inr)

-- Exercises 4.41–42 in Rel. Even if membership cannot be decided,
-- refuting both membership and its negation is contradictory. This
-- gives double-negated excluded middle; cancelling its double negation
-- is exactly where the Boolean hypothesis enters.
module Laws {A B : Set} where
  top bottom : B ← A
  top _ _ = ⊤
  bottom _ _ = ⊥

  not-top : (¬ top) ⊆ bottom
  not-top n = n tt
  not-top′ : bottom ⊆ (¬ top)
  not-top′ ()

  triple : (R : B ← A) → (¬ (¬ (¬ R))) ⊆ (¬ R)
  triple R h r = h (λ nr → nr r)
  triple′ : (R : B ← A) → (¬ R) ⊆ (¬ (¬ (¬ R)))
  triple′ R nr nnr = nnr nr

  module Union (R S : B ← A) = DeMorgan R S

  dense : (R : B ← A) → top ⊆ (¬ (¬ (R ⊔ (¬ R))))
  dense R _ no = no (inr (λ r → no (inl r)))
  dense′ : (R : B ← A) → (¬ (¬ (R ⊔ (¬ R)))) ⊆ top
  dense′ R _ = tt

  Stable = (R : B ← A) → (¬ (¬ R)) ⊆ R
  Decidable = (R : B ← A) → top ⊆ R ⊔ (¬ R)

  decide : Stable → Decidable
  decide stable R {b} {a} u = stable (R ⊔ (¬ R)) (dense R {b} {a} u)
  stabilize : Decidable → Stable
  stabilize dec R {b} {a} nn with dec R {b} {a} tt
  ... | inl r = r
  ... | inr nr with nn nr
  ...   | ()
