{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.DeadlineSort where

open import AoP.Common.Prelude
open import AoP.Chapter10.Tardiness using (Job)
open import AoP.Chapter10.DeadlineMergeOrder using (Sorted; nil; cons)
open import AoP.Chapter10.DeadlineMergeRound using (Runs; Ordered; nil; cons; flat; mass; round; module Pass)
open import AoP.Chapter10.DeadlineRunCount using (passes; one)
open import AoP.Chapter10.DeadlinePassCost using (work; bound)
open import AoP.Chapter10.DeadlineLog using (Budget; choose)
open import AoP.Common.NatOrder using (_≤_; s≤)
open import AoP.Chapter01.ConversionCost using (len)
open import AoP.Chapter05.Permutations using (Perm)
open import AoP.Chapter05.PermuteTail using (identity)
open import AoP.Chapter06.QuickPermutation using (compose)
open import AoP.Chapter01.Naturality using (_++_)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

singles : List Job → Runs
singles [] = []
singles (x ∷ xs) = (x ∷ []) ∷ singles xs
private
  start : ∀ xs → Ordered (singles xs)
  start [] = nil
  start (x ∷ xs) = cons (cons (λ ()) nil) (start xs)
  counted : ∀ xs → len (singles xs) ≡ len xs
  counted [] = refl
  counted (x ∷ xs) = cong suc (counted xs)
  jobs : ∀ xs → mass (singles xs) ≡ len xs
  jobs [] = refl
  jobs (x ∷ xs) = cong suc (jobs xs)
  initial : ∀ xs → flat (singles xs) ≡ xs
  initial [] = refl
  initial (x ∷ xs) = cong (x ∷_) (initial xs)
  perm : ∀ k rs → Perm (flat rs) (flat (passes k rs))
  perm 0 rs = identity _
  perm (suc k) rs = compose (Pass.perm (round rs)) (perm k _)
  order : ∀ k rs → Ordered rs → Ordered (passes k rs)
  order 0 rs p = p
  order (suc k) rs p = order k _ (Pass.sorted (round rs) p)
  unit : ∀ (xs : List Job) → xs ++ [] ≡ xs
  unit [] = refl
  unit (x ∷ xs) = cong (x ∷_) (unit xs)
  finish : ∀ rs → len rs ≤ 1 → Ordered rs → Sorted (flat rs)
  finish [] le nil = nil
  finish (xs ∷ []) le (cons p nil) rewrite unit xs = p
  finish (xs ∷ ys ∷ rs) (s≤ ()) p

rounds : List Job → Nat
rounds xs = Budget.rounds (choose (len xs))
sort : List Job → List Job
sort xs = flat (passes (rounds xs) (singles xs))
permutation : ∀ xs → Perm xs (sort xs)
permutation xs with perm (rounds xs) (singles xs)
... | p rewrite initial xs = p
sorted : ∀ xs → Sorted (sort xs)
sorted xs = finish _ (one (rounds xs) (singles xs) cap) (order (rounds xs) (singles xs) (start xs))
  where cap : len (singles xs) ≤ _
        cap rewrite counted xs = Budget.fits (choose (len xs))
comparisons : ∀ xs → work (rounds xs) (singles xs) ≤ rounds xs * len xs
comparisons xs with bound (rounds xs) (singles xs)
... | p rewrite jobs xs = p
