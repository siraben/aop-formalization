{-# OPTIONS --safe --without-K #-}
module AoP.PivotCalculation where

open import AoP.Prelude
open import AoP.Relations using (_←_; _⊆_; _∘_; _˘)
open import AoP.Shunting using (graph)
open import AoP.Inordered using (flatten)
open import AoP.PivotPermutation using (module Pivot)
open import AoP.PivotFusion using (module Proviso)
open import AoP.PermutationGuard using (module Guard)

-- §6.6. Name the intermediate relations in the quicksort calculation.
-- All have the same endpoints: a pair of trees with a pivot, and a
-- possible output list. The last inclusion is a refinement: the split
-- implementation may choose just one of several valid partitions.
module Steps {A : Set} (R : A ← A) where
  open Pivot {A}
  open Bounds R
  open Proviso R using (Branch; build; children; tree-check; Eligible)
  open Guard {A} using (perm)
  Result = List A ← Branch
  Join = perm ∘ graph join
  Trees = graph children
  checked = check ∘ Trees

  start guarded shuffled moved : Result
  start = perm ∘ (graph flatten ∘ (graph build ∘ tree-check))
  guarded = Join ∘ checked
  shuffled = (Join ∘ Fperm) ∘ checked
  moved = Join ∘ (check ∘ (Fperm ∘ Trees))

  flatten-out : start ⊆ guarded
  flatten-out {a = l , p , r} (_ , permuted , _ , refl , _ , refl , refl , valid) =
    _ , (_ , permuted , refl) , _ , (refl , valid) , refl
  flatten-in : guarded ⊆ start
  flatten-in {a = l , p , r} (_ , (_ , permuted , refl) , _ , (refl , valid) , refl) =
    _ , permuted , _ , refl , _ , refl , refl , valid

  add-perms : guarded ⊆ shuffled
  add-perms (x , j , c) = x , introduce j , c
  drop-perms : shuffled ⊆ guarded
  drop-perms (x , j , c) = x , absorb j , c

  slide-out : shuffled ⊆ moved
  slide-out (x , (y , j , perms) , t , c , trees) with push (x , perms , c)
  ... | z , guarded′ , rearranged = y , j , z , guarded′ , t , rearranged , trees
  slide-in : moved ⊆ shuffled
  slide-in (y , j , z , c , t , rearranged , trees) with pull (z , c , rearranged)
  ... | x , perms , guarded′ = x , (y , j , perms) , t , guarded′ , trees

  module Refine (cut : Triple ← List A) (correct : cut ⊆ Eligible) where
    finish : cut ˘ ∘ (Fperm ∘ Trees) ⊆ moved
    finish (z , c , ps) with correct c
    ... | valid , permutation = z , (_ , permutation , refl) , z , (refl , valid) , ps
    proviso : cut ˘ ∘ (Fperm ∘ Trees) ⊆ start
    proviso {a = t} x = flatten-in {a = t} (drop-perms {a = t} (slide-in {a = t} (finish {a = t} x)))
