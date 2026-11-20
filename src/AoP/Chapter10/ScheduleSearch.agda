{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.ScheduleSearch where

open import AoP.Common.Prelude
open import AoP.Chapter10.Tardiness using (Job; cost)
open import AoP.Chapter01.Snoc using (toSnoc)
open import AoP.Chapter05.Permutations using (Perm; empty; insert; front; perms; complete; sound)
open import AoP.Common.FiniteMinimum using (module Search)
open import AoP.Chapter02.Polynomial using (inl)
open import AoP.Common.NatOrder using (_≤_)
open import Agda.Builtin.Nat using (Nat)

-- §10.3. Before deriving a greedy scheduler, establish a reference
-- implementation of the specification: every occurrence in the input
-- is a job to schedule, even if two job records happen to be equal.
-- Consider all permutations and minimize the maximum tardiness. This
-- baseline is factorial; unlike a three-job example its correctness
-- certificate compares the result against every order for any input.
score : List Job → Nat
score xs = cost (toSnoc xs)

module Candidates = Search (λ (_ : List Job) → ⊤) (λ _ → inl tt) score

unchanged : (xs : List Job) → Perm xs xs
unchanged [] = empty
unchanged (j ∷ js) = insert (unchanged js) front

record Solution (js : List Job) : Set where
  constructor scheduled
  field
    order : List Job
    feasible : Perm js order
    minimal : ∀ xs → Perm js xs → score order ≤ score xs

solve : ∀ js → Solution js
solve js with Candidates.scan (perms js)
... | Candidates.none no with no js (complete (unchanged js)) tt
...   | ()
solve js | Candidates.best xs member _ least = scheduled xs (sound js member)
  (λ ys perm → least ys (complete perm) tt)
