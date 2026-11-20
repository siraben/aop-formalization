{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.PivotFusion where

open import AoP.Common.Prelude
open import AoP.Chapter06.Inordered using (Tree; fork; flatten)
open import AoP.Chapter06.PivotPermutation using (module Pivot)
open import AoP.Chapter05.Permutations using (Perm; insert; front)
open import AoP.Chapter06.QuickPermutation using (compose; append-perm)
open import AoP.Chapter06.PermutationGuard using (module Guard)
open import AoP.Chapter04.Relations using (_←_; _⊆_; _˘; _∘_)
open import AoP.Chapter04.Shunting using (graph)

-- §6.6. The fusion proviso quantifies over two arbitrary subtrees.
-- Flatten and permute their labels, then run a valid split backwards.
-- We must be able to reach the same list by first checking the trees,
-- forking them, flattening the fork, and permuting its labels once.
module Proviso {A : Set} (R : A ← A) where
  open Pivot {A}
  open Bounds R using (Valid)
  open Guard {A} using (perm; forward)
  Branch = Tree A × (A × Tree A)
  build : Branch → Tree A
  build (l , p , r) = fork l p r
  children : Branch → Triple
  children (l , p , r) = flatten l , p , flatten r

  tree-check : Branch ← Branch
  tree-check y x = (y ≡ x) × Valid (children x)

  -- The relational split specification allows any input-equivalent
  -- pivot partition, so the result applies to every conforming split.
  Eligible : Triple ← List A
  Eligible triple xs = Valid triple × Perm (join triple) xs

  module Law (split : Triple ← List A) (correct : split ⊆ Eligible) where
    fusion : split ˘ ∘ (Fperm ∘ graph children) ⊆ perm ∘ (graph flatten ∘ (graph build ∘ tree-check))
    fusion {a = l , p , r} (_ , cut , _ , (lp , refl , rp) , refl) with correct cut
    ... | (lo , hi) , permutation = _ , total , _ , refl , _ , refl , refl , bounds
      where
      -- Membership travels forward into the permuted lists to recover
      -- the pivot bounds on the original labels of each subtree.
      bounds : Valid (children (l , p , r))
      bounds = (λ m → lo (forward lp m)) , (λ m → hi (forward rp m))
      total = compose (append-perm lp (insert rp front)) permutation
