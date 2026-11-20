{-# OPTIONS --safe --without-K #-}
module AoP.DeadlineRun where

open import AoP.Prelude
open import AoP.Tardiness using (Job)
open import AoP.EqualWeightDeadline using (least-charge)
open import AoP.PickLast using (picked)
open import AoP.BackwardSchedule using (Run; stop; choose; snoc; last-slot)
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.NatOrder using (_≤_; rid)
open import AoP.TardinessBound using (charge)
open import AoP.ScheduleDuration using (total)
open import Agda.Builtin.Nat using (Nat)
open Job

-- A schedule in earliest-deadline order is built by appending a job
-- after a prefix whose deadlines are all no later. The weight witness
-- is retained at each step, including the first job of an empty prefix.
data Ordered (w : Nat) : List Job → Set where
  nil : Ordered w []
  append : ∀ {xs} j → Ordered w xs → weight j ≡ w →
           (∀ x → x ∈ xs → (weight x ≡ w) × (due x ≤ due j)) → Ordered w (snoc xs j)

private
  all-snoc : ∀ (P : Job → Set) xs j → (∀ x → x ∈ xs → P x) → P j → ∀ x → x ∈ snoc xs j → P x
  all-snoc P [] j old end .j here = end
  all-snoc P [] j old end x (there ())
  all-snoc P (a ∷ xs) j old end .a here = old a here
  all-snoc P (a ∷ xs) j old end x (there m) = all-snoc P xs j (λ z p → old z (there p)) end x m
  back : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  back refl = refl

run : ∀ {w xs} → Ordered w xs → Run xs xs
run nil = stop
run (append {[]} j ord eq bound) = choose j [] (picked j [] (last-slot [] j) (all-snoc _ [] j (λ _ ()) (rid _))) stop
run (append {a ∷ xs} j ord eq bound) = choose a (snoc xs j) (picked j (a ∷ xs) (last-slot _ j) cheap) (run ord)
  where t = total (a ∷ snoc xs j)
        cheap : ∀ x → x ∈ snoc (a ∷ xs) j → charge j t ≤ charge x t
        cheap = all-snoc _ (a ∷ xs) j (λ x m → least-charge x j t (fst (bound x m) ∙ back eq) (snd (bound x m))) (rid _)
