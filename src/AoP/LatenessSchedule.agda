{-# OPTIONS --safe --without-K #-}
module AoP.LatenessSchedule where

open import AoP.Prelude
open import AoP.Tardiness using (Job)
open import AoP.ScheduleDuration using (total)
open import AoP.BackwardSchedule using (length; smaller; snoc; last-slot; reinsert)
open import AoP.LatenessPick using (Pick; pick)
open import AoP.Permutations using (Perm; empty)
open import AoP.NatOrder using (_≤_; rid)
open import Agda.Builtin.Nat using (Nat; suc)

-- Exercise 10.10. Recompute the common completion time after removing
-- each chosen occurrence. The recursive schedule is a permutation of
-- the remainder; appending the chosen occurrence restores the input bag.
data Run : List Job → List Job → Set where
  stop : Run [] []
  choose : ∀ j js {out} (p : Pick (total (j ∷ js)) (j ∷ js)) →
           Run (Pick.others p) out → Run (j ∷ js) (snoc out (Pick.last p))

permutation : ∀ {xs ys} → Run xs ys → Perm xs ys
permutation stop = empty
permutation (choose j js p r) = reinsert (Pick.occurrence p) (permutation r) (last-slot _ _)

private
  loop : ∀ n jobs → length jobs ≤ n → Σ _ (Run jobs)
  loop n [] b = [] , stop
  loop (suc n) (j ∷ js) b with pick (total (j ∷ js)) j js
  ... | p with loop n (Pick.others p) (smaller (Pick.occurrence p) b)
  ...   | out , r = snoc out (Pick.last p) , choose j js p r

schedule : ∀ jobs → Σ _ (Run jobs)
schedule jobs = loop (length jobs) jobs (rid _)
