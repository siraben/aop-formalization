{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.BackwardExample where

open import AoP.Common.Prelude
open import AoP.Chapter10.TardinessExample using (A; B; C)
open import AoP.Chapter10.Tardiness using (Job)
open import AoP.Chapter10.BackwardSchedule using (schedule)
open import AoP.Chapter10.GreedyTardinessCost using (peak; optimal)
open import AoP.Chapter05.Permutations using (Perm)
open import AoP.Common.NatOrder using (_≤_)

-- §10.3, run the actual algorithm. A, B, C take 5, 10, 15 units;
-- their due times are 10, 20, 20 and their weights are 1, 3, 3.
-- At time 30 the last-job penalties are 20, 30, 30: place A last.
-- At time 25 the remaining jobs tie at 15: pick B (first in the
-- input) to go before A. This tie explains why the output is C,B,A
-- rather than the equally good B,C,A. The proof below does not rely
-- on enumerating the six orders: instantiate the general greedy law.
jobs : List Job
jobs = A ∷ B ∷ C ∷ []

computed : fst (schedule jobs) ≡ C ∷ B ∷ A ∷ []
computed = refl

score : peak 0 (fst (schedule jobs)) ≡ 20
score = refl

cannot-improve : ∀ xs → Perm jobs xs → 20 ≤ peak 0 xs
cannot-improve xs = optimal (snd (schedule jobs))
