{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.Tardiness where

open import AoP.Common.Prelude
open import AoP.Chapter01.Snoc using (Snoc; ε; _▻_; foldl)
open import AoP.Chapter01.Trees using (max)
open import Agda.Builtin.Nat using (Nat; _+_; _*_; _-_)

-- §10.3. A machine processes jobs one at a time. A late job incurs its
-- weight times the number of time units late; an early job costs zero.
-- Scheduling asks for a permutation minimizing the *largest* penalty,
-- not the total. To evaluate a schedule, remember its elapsed time too:
-- the next penalty depends on when the newly appended job finishes.
record Job : Set where
  constructor job
  field duration due weight : Nat
open Job

elapsed : Snoc Job → Nat
elapsed = foldl 0 (λ t j → t + duration j)

penalty : Nat → Job → Nat
penalty t j = ((t + duration j) - due j) * weight j

cost : Snoc Job → Nat
cost ε = 0
cost (s ▻ j) = max (cost s) (penalty (elapsed s) j)

step : Nat × Nat → Job → Nat × Nat
step (t , c) j = (t + duration j) , max c (penalty t j)

-- Fuse the two traversals into one; in particular the evaluator does
-- not rescan all preceding jobs for every new completion time.
profile : Snoc Job → Nat × Nat
profile = foldl (0 , 0) step

correct : ∀ s → profile s ≡ (elapsed s , cost s)
correct ε = refl
correct (s ▻ j) = begin
  step (profile s) j              ≡⟨ cong (λ p → step p j) (correct s) ⟩
  step (elapsed s , cost s) j     ≡⟨⟩
  (elapsed (s ▻ j) , cost (s ▻ j)) ∎

-- The final job finishes 20 units late with weight 1. The middle job's
-- penalty is 15, so the objective is 20 rather than 35.
example : profile (((ε ▻ job 10 20 3) ▻ job 15 20 3) ▻ job 5 10 1) ≡ (30 , 20)
example = refl
