{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.KnapsackSortedTable where

open import AoP.Common.Prelude
open import AoP.Chapter08.KnapsackFrontier using (Summary; module Sweep)
open import AoP.Chapter08.KnapsackSortedBranches using (Desc; module Branch)
open import AoP.Chapter08.KnapsackMerge using (merge; ordered; sample)
open import AoP.Chapter06.OrderedMeet using (module Order)
open import AoP.Chapter08.SortedSubset using (module Sort)
open import Agda.Builtin.Nat using (Nat)

-- §8.4. Fold over items, keeping feasible take candidates and skip
-- candidates in one list sorted by descending value. Bumping removes
-- entries without changing their relative order.
module Table (cap : Nat) where
  stream : Summary → List Summary → List Summary
  stream i xs = fst (merge (Branch.take cap i xs) xs)
  advance : Summary → List Summary → List Summary
  advance i xs = Sweep.thinlist (stream i xs)
  table : List Summary → List Summary
  table [] = (0 , 0) ∷ []
  table (i ∷ is) = advance i (table is)

  invariant : ∀ is → Order.Ordered Desc (table is)
  invariant [] = Order.cons (λ ()) Order.nil
  invariant (i ∷ is) = Sort.ordered-sub Desc (Sweep.ordered (stream i xs))
    (ordered (snd (merge (Branch.take cap i xs) xs)) (Branch.take-order cap i sorted) sorted)
    where xs = table is
          sorted = invariant is

-- (3,5) loses to (3,7); (2,3) loses to (1,4). The zero pack remains
-- useful because future items can require all of the capacity.
survivors : Table.advance 3 (2 , 3) sample ≡ (3 , 7) ∷ (1 , 4) ∷ (0 , 0) ∷ []
survivors = refl
