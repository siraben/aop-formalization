{-# OPTIONS --safe --without-K #-}
module AoP.DeadlineMergePermutation where

open import AoP.Prelude
open import AoP.DeadlineMerge
open import AoP.Tardiness using (Job)
open import AoP.Naturality using (_++_)
open import AoP.Permutations using (Perm; empty; front; insert)
open import AoP.QuickPermutation using (skip)
open import AoP.BackwardSchedule using (reinsert)
open import AoP.PermuteTail using (identity)

-- A comparison selects a particular occurrence. For a right choice,
-- the occurrence initially follows the whole left run; reinsert it at
-- the front of the recursively merged tail. No job equality is needed.
private
  finish : ∀ (xs : List Job) → Perm (xs ++ []) xs
  finish [] = empty
  finish (x ∷ xs) = insert (finish xs) front

preserves : ∀ {xs ys zs} → Trace xs ys zs → Perm (xs ++ ys) zs
preserves (left-empty ys) = identity ys
preserves (right-empty xs) = finish xs
preserves (left _ tr) = insert (preserves tr) front
preserves (right {x} {xs} _ tr) = reinsert (skip (x ∷ xs) front) (preserves tr) front
