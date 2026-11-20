{-# OPTIONS --safe --without-K #-}
module AoP.EqualWeightSchedule where

open import AoP.Prelude
open import AoP.Tardiness using (Job)
open import AoP.DeadlineSort using (sort; permutation; sorted)
open import AoP.DeadlineMergeOrder using (Bound; Sorted; nil; cons)
open import AoP.DeadlineRun using (Ordered; nil; append)
open import AoP.DeadlineCertificate using (certified)
open import AoP.BackwardSchedule using (snoc)
open import AoP.ScheduleSearch using (Solution)
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.PermutationGuard using (module Guard)
open import Agda.Builtin.Nat using (Nat)
open Job

private
  last : ∀ xs j → j ∈ snoc xs j
  last [] j = here
  last (x ∷ xs) j = there (last xs j)
  keep : ∀ xs j {y} → y ∈ xs → y ∈ snoc xs j
  keep (x ∷ xs) j here = here
  keep (x ∷ xs) j (there m) = there (keep xs j m)

  prepend : ∀ {w xs} x → weight x ≡ w → Bound x xs → Ordered w xs → Ordered w (x ∷ xs)
  prepend x eq b nil = append x nil eq (λ _ ())
  prepend x eq b (append {xs} j ord ej prev) = append j
    (prepend x eq (λ m → b (keep xs j m)) ord) ej λ where
    .x here → eq , b (last xs j)
    y (there m) → prev y m

Uniform : Nat → List Job → Set
Uniform w xs = ∀ {x} → x ∈ xs → weight x ≡ w

convert : ∀ {xs w} → Sorted xs → Uniform w xs → Ordered w xs
convert nil u = nil
convert (cons {j} b s) u = prepend j (u here) b (convert s (λ m → u (there m)))

-- Sort only by deadline. Transport the common-weight assumption to
-- every output occurrence, then apply the backward scheduling theorem.
schedule : ∀ {w} jobs → Uniform w jobs → Solution jobs
schedule jobs u = certified (permutation jobs) (convert (sorted jobs) (λ m → u (Guard.backward (permutation jobs) m)))
