{-# OPTIONS --safe --without-K #-}
module AoP.SumTardiness where

open import AoP.Prelude
open import AoP.Snoc using (Snoc; ε; _▻_)
open import AoP.Tardiness using (Job; job; elapsed; penalty)
open import AoP.NatOrder using (_≤_; rid; weaken)
open import Agda.Builtin.Nat using (Nat; _+_; suc)

-- Exercise 10.11. Try the chapter's minimum-final-penalty rule on
-- the sum objective. Both jobs are due at time zero. The long job
-- takes three ticks and has weight two; the short job takes one tick
-- and has weight one. Both orders finish at time four.
sum-cost : Snoc Job → Nat
sum-cost ε = 0
sum-cost (s ▻ j) = sum-cost s + penalty (elapsed s) j

long short : Job
long = job 3 0 2
short = job 1 0 1

-- As last job, short pays 4 and long pays 8, so the rule strictly
-- prefers short last. But that order pays 6+4; the reverse pays 1+8.
picks-short : suc (penalty (elapsed (ε ▻ long)) short) ≤ penalty (elapsed (ε ▻ short)) long
picks-short = weaken (weaken (weaken (rid 5)))

witness : suc (sum-cost (ε ▻ short ▻ long)) ≤ sum-cost (ε ▻ long ▻ short)
witness = rid 10
