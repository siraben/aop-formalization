{-# OPTIONS --safe --without-K #-}
module AoP.ScheduleThreshold where

open import AoP.Prelude
open import AoP.Permutations using (Insert; front; later; Perm; empty; insert)
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.PickLast using (Pick)
open import AoP.ScheduleDuration using (total; perm-total)
open import AoP.Tardiness using (Job)
open import AoP.TardinessBound using (module Limit)
open import AoP.LastBound using (module Witness)
open import AoP.NatOrder using (chain)
open import Agda.Builtin.Nat using (Nat)

-- §10.3. Even though the competitor need not end with the greedy job,
-- it ends with *some* input job. Compare both penalties at that same
-- finish time, using the bag invariant to change representations.
split-slot : ∀ {A : Set} {j x : A} {xs ys} → Insert j xs ys → x ∈ ys → (j ≡ x) ⊎ (x ∈ xs)
split-slot front here = inl refl
split-slot front (there m) = inr m
split-slot (later i) here = inr here
split-slot (later i) (there m) with split-slot i m
... | inl eq = inl eq
... | inr p = inr (there p)

original : ∀ {A : Set} {x : A} {xs ys} → Perm xs ys → x ∈ ys → x ∈ xs
original (insert p i) m with split-slot i m
... | inl refl = here
... | inr q = there (original p q)

module Bound (k : Nat) where
  open Limit k
  open Witness k
  last-ok : ∀ {jobs y ys} (p : Pick (total jobs) jobs) → Perm jobs (y ∷ ys) →
            Fits 0 (y ∷ ys) → Allowed (Pick.last p) (total jobs)
  last-ok {jobs} {y} {ys} p perm fits with final-job y ys fits
  ... | z , mem , ok rewrite finish-total 0 (y ∷ ys) | perm-total perm =
    chain (Pick.cheapest p z (original perm mem)) ok
