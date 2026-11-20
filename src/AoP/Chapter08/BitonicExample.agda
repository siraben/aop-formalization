{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.BitonicExample where

open import AoP.Common.Prelude
open import AoP.Chapter08.BitonicTable using (module DP)
open import Agda.Builtin.Nat using (Nat; _+_; _*_) renaming (_-_ to _∸_)

-- Four stops are numbered from west to east. Travel between two stops
-- costs the square of their separation. Start at 0, turn at 3, and visit
-- each interior stop once, travelling east before the turn and west after.
-- Visiting both intermediate stops on the way out leaves an expensive
-- direct return: 0 → 1 → 2 → 3 → 0 costs 1 + 1 + 1 + 9 = 12.
edge : Nat → Nat → Nat
edge u v = gap * gap where gap = (u ∸ v) + (v ∸ u)

open DP edge 3
open import AoP.Chapter08.Bitonic using (module Tours)
open Tours edge

answer : Cell 0 0 (1 ∷ 2 ∷ [])
answer = tour-table 0 (1 ∷ 2 ∷ [])

-- The table sends stop 1 to the outward leg and 2 to the homeward leg:
-- 0 → 1 → 3 → 2 → 0 costs 1 + 4 + 1 + 4. Reversing it gives a tie.
route-found : Cell.route answer ≡ outward (homeward close)
route-found = refl

price-found : Cell.price answer ≡ 10
price-found = refl

open import AoP.Common.NatOrder using (_≤_)
minimum : (q : Route (1 ∷ 2 ∷ [])) → 10 ≤ cost 0 0 3 q
minimum = Cell.least answer
