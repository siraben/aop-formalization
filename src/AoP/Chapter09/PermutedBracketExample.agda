{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.PermutedBracketExample where

open import AoP.Common.Prelude
open import AoP.Chapter09.DecimalBracketCost using (module Sum)
open import AoP.Chapter09.DecimalBracketMinimum using (module Add)
open import AoP.Chapter09.PermutedMinimum using (module Optimize)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 9.15. Fixed order forces the first addition to involve 9:
-- adding either neighbour produces 10, so the second addition takes
-- two columns. Reordering lets us add the two ones first. The solvers
-- certify these are the respective optima, not just two candidate costs.
remaining : List Nat
remaining = 9 ∷ 1 ∷ []  -- the nonempty input is 1 ∷ remaining
fixed = Add.Best.tree (Add.solve 1 remaining)
free = fst (Optimize.solve Sum.cost 1 remaining)
fixed-columns : Sum.cost fixed ≡ 3
fixed-columns = refl
free-columns : Sum.cost free ≡ 2
free-columns = refl
same-sum : Sum.size fixed ≡ Sum.size free
same-sum = refl
sum-value : Sum.size free ≡ 11
sum-value = refl
