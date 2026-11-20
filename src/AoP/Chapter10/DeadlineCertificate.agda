{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.DeadlineCertificate where

open import AoP.Common.Prelude
open import AoP.Chapter10.DeadlineRun using (Ordered; run)
open import AoP.Chapter10.Tardiness using (Job)
open import AoP.Chapter10.ScheduleSearch using (Solution; scheduled)
open import AoP.Chapter10.ScheduleCertificate using (agreement)
open import AoP.Chapter10.GreedyTardinessCost using (optimal)
open import AoP.Chapter10.BackwardSchedule using (reinsert)
open import AoP.Chapter05.Permutations using (Perm; front; empty; insert)
open import AoP.Chapter06.QuickPermutation using (compose)
open import AoP.Common.NatOrder using (_≤_)

-- A sorting implementation may choose any permutation in due-date
-- order. Its schedule competes with every permutation of the original
-- jobs, even if jobs with the same due date occur in a different order.
private
  reverse-perm : ∀ {xs ys : List Job} → Perm xs ys → Perm ys xs
  reverse-perm empty = empty
  reverse-perm (insert p i) = reinsert i (reverse-perm p) front
  transfer : ∀ {a b c d} → a ≡ b → c ≡ d → b ≤ d → a ≤ c
  transfer refl refl p = p

certified : ∀ {w jobs xs} → Perm jobs xs → Ordered w xs → Solution jobs
certified {xs = xs} order sorted = scheduled xs order λ ys competitor →
  transfer (agreement xs) (agreement ys) (optimal (run sorted) (compose (reverse-perm order) competitor))
