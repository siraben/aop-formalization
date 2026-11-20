{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.CachedVanTie where

open import AoP.Common.Prelude
open import AoP.Chapter07.Reserves using (Tx)
open import AoP.Chapter07.CachedVan using (module Cached)
open import AoP.Chapter07.CachedVanDecisions using (module Law)
open import AoP.Chapter07.CachedVanOptimal using (module Certificate)
open import AoP.Chapter07.VanFold using (module Fold)
open import AoP.Chapter07.VanSchedule using (module Schedule)
open import AoP.Chapter07.VanHeadOrder using () renaming (module Law to Head)
open import AoP.Chapter07.VanGreedyDominance using (module Proof)
open import AoP.Chapter07.SecurePartitionFold using () renaming (module Law to Guard)
open import AoP.Chapter08.LineBreaks using (module Breaks)
open import AoP.Common.NatOrder using (_≤_; s≤)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat; suc)

-- Exercise 7.54. If another feasible partition ties the cached right
-- fold in internal visits, the first block of the greedy answer must
-- be a prefix of the competitor's. This fixes the direction of ties.
module Tie (cap : Nat) where
  open Cached cap
  open Fold cap using (Serviceable)
  open Schedule cap using (Valid; visits)
  open Breaks (λ (_ : Tx) → 0) 0 using (Partition)
  open Head Tx using (H; count)
  open Certificate cap using (blocks)
  private
    absurd : ∀ {k} {X : Set} → suc k ≤ k → X
    absurd {0} ()
    absurd {suc k} (s≤ p) = absurd p
    back : ∀ {i j : Nat} → i ≡ j → j ≡ i
    back refl = refl
  prefix : ∀ t ts (s : Serviceable (t ∷ ts)) q → Partition t ts q → Valid q →
           visits (Result.plan (solve t ts s)) ≡ visits q → H (Result.plan (solve t ts s)) q
  prefix t ts s q part ok tie with Proof.dominates cap (Law.follows cap t ts s) (Guard.complete cap part ok)
  ... | inr (_ , h) = h
  ... | inl lt with blocks (Result.plan (solve t ts s)) ∙ cong suc tie ∙ back (blocks q)
  ...   | eq rewrite eq = absurd lt
