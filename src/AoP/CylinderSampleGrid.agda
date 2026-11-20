{-# OPTIONS --safe --without-K #-}
module AoP.CylinderSampleGrid where

open import AoP.Prelude
open import AoP.CylinderFiniteRim using (Row; top; below; up; down)
open import AoP.Cylinder using (module Grid)
open import AoP.CylinderCachedColumn using (module Table)
open import AoP.CylinderTableWinner using (module Cylinder)
open import Agda.Builtin.Nat using (Nat)
open Grid (Row 5) up down using (Column; Path; cost; exit; rise; stay; fall)
open Table (Row 5) up down using (Cell)
open Cylinder 4

-- The ten columns in the worked §7.4 grid, each read from top to bottom.
col : Nat → Nat → Nat → Nat → Nat → Column
col a b c d e top = a
col a b c d e (below top) = b
col a b c d e (below (below top)) = c
col a b c d e (below (below (below top))) = d
col a b c d e (below (below (below (below top)))) = e

entry = col 11 4 67 24 99
rest = col 53 72 22 71 8 ∷ col 34 24 10 46 57 ∷ col 73 6 97 62 76 ∷
       col 18 46 99 18 7 ∷ col 53 17 64 11 51 ∷ col 99 63 33 54 90 ∷
       col 52 82 45 40 92 ∷ col 31 89 81 17 51 ∷ col 54 25 76 51 21 ∷ []

-- Following the highlighted route gives 429. The figure illustrates
-- feasibility; the suffix table finds a cheaper route on the same cells.
shown : Path rest
shown = fall (fall (stay (stay (rise (fall (rise (rise (stay exit))))))))
example-cost : cost entry (below top) shown ≡ 429
example-cost = refl

answer : Winner entry rest
answer = optimum entry rest
optimal-score : Cell.score (Winner.selected answer) ≡ 188
optimal-score = refl
