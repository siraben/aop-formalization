{-# OPTIONS --safe --without-K #-}
module AoP.TeXClosestPrinter where

open import AoP.Prelude
open import AoP.TeXFraction using (Digit)
open import AoP.TeXExternal using (Shortest; zero-shortest)
open import AoP.TeXClosestShortest using (Closest; winner)
open import AoP.TeXNearestShortest using (module Improve)
import AoP.TeXSinglePrinter as Greedy
open import AoP.NatOrder using (_≤_; z≤)
open import Agda.Builtin.Nat using (Nat; suc)

-- Exercise 10.15. Use the greedy loop only to obtain the minimum
-- width and one admissible numerator. Choose the nearest admissible
-- numerator at that width and render it, keeping leading zeroes.
extern : ∀ n → suc n ≤ 65536 → Σ (List Digit) (Closest n)
extern 0 _ = [] , winner zero-shortest (λ _ _ _ → z≤)
extern (suc t) bound = refine (Greedy.extern (suc t) bound)
  where refine : Σ (List Digit) (Shortest (suc t)) → Σ (List Digit) (Closest (suc t))
        refine (ds , ok) = Improve.solution t ds ok
