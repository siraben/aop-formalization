{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.DeadlineMergePermutation where

open import AoP.Common.Prelude
open import AoP.Chapter10.DeadlineMerge
open import AoP.Chapter10.Tardiness using (Job)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter05.Permutations using (Perm; empty; front; insert)
open import AoP.Chapter06.QuickPermutation using (skip)
open import AoP.Chapter10.BackwardSchedule using (reinsert)
open import AoP.Chapter05.PermuteTail using (identity)

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
