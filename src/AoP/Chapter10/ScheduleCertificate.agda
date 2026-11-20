{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.ScheduleCertificate where

open import AoP.Common.Prelude
open import AoP.Chapter10.Tardiness
open import AoP.Chapter10.ScheduleSearch using (Solution; scheduled; score)
open import AoP.Chapter10.BackwardSchedule using (schedule; permutation)
open import AoP.Chapter10.GreedyTardinessCost using (peak; optimal)
open import AoP.Chapter01.Snoc using (Snoc; ε; _▻_; append; toSnoc)
open import AoP.Chapter01.Trees using (max)
open import AoP.Common.NatOrder using (_≤_; z≤)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- Tie the backward program to the *same specification* used by exhaustive
-- search. `peak` processes a cons-list from a known starting time;
-- `cost` processes snoc-lists, retaining the maximum over the prefix.
-- The accumulator law accounts for both that prefix and the suffix.
private
  right-zero : ∀ a → max a 0 ≡ a
  right-zero zero = refl
  right-zero (suc _) = refl

  assoc : ∀ a b c → max (max a b) c ≡ max a (max b c)
  assoc zero b c = refl
  assoc (suc a) zero c = refl
  assoc (suc a) (suc b) zero = refl
  assoc (suc a) (suc b) (suc c) = cong suc (assoc a b c)

  back : ∀ {a b : Nat} → a ≡ b → b ≡ a
  back refl = refl

accumulate : ∀ prefix xs → cost (append prefix xs) ≡ max (cost prefix) (peak (elapsed prefix) xs)
accumulate p [] = back (right-zero (cost p))
accumulate p (j ∷ js) = begin
  cost (append (p ▻ j) js) ≡⟨ accumulate (p ▻ j) js ⟩
  max (cost (p ▻ j)) (peak (elapsed (p ▻ j)) js)
    ≡⟨ assoc (cost p) (penalty (elapsed p) j) (peak (elapsed (p ▻ j)) js) ⟩
  max (cost p) (peak (elapsed p) (j ∷ js)) ∎

agreement : ∀ xs → score xs ≡ peak 0 xs
agreement xs = accumulate ε xs

-- No permutation enumeration is used by this certified implementation.
greedy : ∀ jobs → Solution jobs
greedy jobs with schedule jobs
... | out , run = scheduled out (permutation run) λ xs perm →
  transfer (agreement out) (agreement xs) (optimal run perm)
  where
  transfer : ∀ {a b c d} → a ≡ b → c ≡ d → b ≤ d → a ≤ c
  transfer refl refl le = le
