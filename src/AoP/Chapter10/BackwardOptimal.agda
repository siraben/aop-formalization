{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.BackwardOptimal where

open import AoP.Common.Prelude
open import AoP.Chapter05.Permutations using (Perm; insert)
open import AoP.Chapter10.PermuteRemoval using (remove-permuted)
open import AoP.Chapter10.BackwardSchedule using (Run; stop; choose; permutation; snoc)
open import AoP.Chapter10.TardinessBound using (module Limit)
open import AoP.Chapter10.Tardiness using (Job)
open import AoP.Chapter10.ScheduleDuration using (total; perm-total)
open import AoP.Chapter10.ScheduleThreshold using (module Bound)
open import AoP.Chapter10.LastBound using (module Witness)
open import AoP.Chapter10.PickLast using (Pick)
open import Agda.Builtin.Nat using (Nat; _+_)

-- §10.3, optimality in threshold form. Fix an arbitrary penalty cap k.
-- If any permutation meets it, the backward greedy schedule meets it too.
-- Delete the chosen job from the competitor, use induction on the smaller
-- bag, then restore that job at the end. Its finish time depends only on
-- the original bag, not on either ordering of the remaining jobs.
module Threshold (k : Nat) where
  open Limit k
  open Witness k
  open Bound k using (last-ok)

  snoc-finish : ∀ s xs j → finish s (snoc xs j) ≡ finish s xs + Job.duration j
  snoc-finish s [] j = refl
  snoc-finish s (x ∷ xs) j = snoc-finish (s + Job.duration x) xs j

  attach : ∀ {s xs} j → Fits s xs → Allowed j (finish s (snoc xs j)) → Fits s (snoc xs j)
  attach j empty ok = step ok empty
  attach j (step ready tail) ok = step ready (attach j tail ok)

  cast : ∀ j {a b} → a ≡ b → Allowed j b → Allowed j a
  cast j refl ok = ok

  transport-run : ∀ {jobs out ys} → Run jobs out → Perm jobs ys → Fits 0 ys → Fits 0 out
  transport-run stop _ _ = empty
  transport-run (choose j js p r) (insert perm ()) empty
  transport-run run@(choose j js {out} p r) perm competitor@(step {j = y} {js = ys} _ _) with remove-permuted (Pick.restore p) perm
  ... | rest , smaller , slot = attach last (transport-run r smaller (opens-slot slot competitor))
                                  (cast last end-time (last-ok p perm competitor))
    where
    last = Pick.last p
    end-time : finish 0 (snoc out last) ≡ total (j ∷ js)
    end-time = begin
      finish 0 (snoc out last) ≡⟨ finish-total 0 (snoc out last) ⟩
      total (snoc out last)   ≡⟨ perm-total (permutation run) ⟩
      total (j ∷ js) ∎
