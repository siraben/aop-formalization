{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.LatenessThreshold where

open import AoP.Common.Prelude
open import AoP.Chapter10.LatenessExchange using (module Limit)
open import AoP.Chapter10.LatenessPick using (Pick)
open import AoP.Chapter10.LatenessSchedule using (Run; stop; choose; permutation)
open import AoP.Chapter10.ScheduleDuration using (total; perm-total)
open import AoP.Chapter10.ScheduleThreshold using (original)
open import AoP.Chapter10.LastBound using (module Witness)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Chapter10.PermuteRemoval using (remove-permuted)
open import AoP.Chapter05.Permutations using (Perm; insert)
open import AoP.Chapter10.BackwardSchedule using (snoc)
open import AoP.Chapter07.SignedSegment using (chain)
open import AoP.Chapter10.Tardiness using (Job)
open import Agda.Builtin.Int using (Int)
open import Agda.Builtin.Nat using (_+_)

-- Every integer ceiling achievable by a competitor is achievable by
-- the greedy schedule. Use the competitor's actual last job to bound
-- the chosen job; removing the latter moves intervening jobs earlier.
module Bound (k : Int) where
  open Limit k
  finish-total : ∀ s js → finish s js ≡ s + total js
  finish-total s [] = Witness.unit 0 s
  finish-total s (j ∷ js) = finish-total (s + Job.duration j) js ∙ Witness.assoc 0 s (Job.duration j) (total js)
  last-job : ∀ {s} j js → Fits s (j ∷ js) → Σ Job λ z → (z ∈ (j ∷ js)) × Allowed z (finish s (j ∷ js))
  last-job j [] (step ok empty) = j , here , ok
  last-job j (h ∷ t) (step _ rest) with last-job h t rest
  ... | z , mem , ok = z , there mem , ok
  last-ok : ∀ {jobs y ys} (p : Pick (total jobs) jobs) → Perm jobs (y ∷ ys) → Fits 0 (y ∷ ys) → Allowed (Pick.last p) (total jobs)
  last-ok {jobs} {y} {ys} p perm fits with last-job y ys fits
  ... | z , mem , ok rewrite finish-total 0 (y ∷ ys) | perm-total perm = chain (Pick.least p z (original perm mem)) ok

  attach : ∀ {s xs} j → Fits s xs → Allowed j (finish s (snoc xs j)) → Fits s (snoc xs j)
  attach j empty ok = step ok empty
  attach j (step ready tail) ok = step ready (attach j tail ok)
  cast : ∀ j {a b} → a ≡ b → Allowed j b → Allowed j a
  cast j refl ok = ok
  transport : ∀ {jobs out ys} → Run jobs out → Perm jobs ys → Fits 0 ys → Fits 0 out
  transport stop _ _ = empty
  transport (choose j js p r) (insert perm ()) empty
  transport run@(choose j js {out} p r) perm fits@(step _ _) with remove-permuted (Pick.occurrence p) perm
  ... | rest , smaller , slot = attach z (transport r smaller (opens-slot slot fits))
    (cast z (finish-total 0 (snoc out z) ∙ perm-total (permutation run)) (last-ok p perm fits))
    where z = Pick.last p
