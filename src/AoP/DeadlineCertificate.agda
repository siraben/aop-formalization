{-# OPTIONS --safe --without-K #-}
module AoP.DeadlineCertificate where

open import AoP.Prelude
open import AoP.DeadlineRun using (Ordered; run)
open import AoP.Tardiness using (Job)
open import AoP.ScheduleSearch using (Solution; scheduled)
open import AoP.ScheduleCertificate using (agreement)
open import AoP.GreedyTardinessCost using (optimal)
open import AoP.BackwardSchedule using (reinsert)
open import AoP.Permutations using (Perm; front; empty; insert)
open import AoP.QuickPermutation using (compose)
open import AoP.NatOrder using (_≤_)

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
