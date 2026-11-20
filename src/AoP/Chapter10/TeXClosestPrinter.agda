{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXClosestPrinter where

open import AoP.Common.Prelude
open import AoP.Chapter03.TeXFraction using (Digit)
open import AoP.Chapter10.TeXExternal using (Shortest; zero-shortest)
open import AoP.Chapter10.TeXClosestShortest using (Closest; winner)
open import AoP.Chapter10.TeXNearestShortest using (module Improve)
import AoP.Chapter10.TeXSinglePrinter as Greedy
open import AoP.Common.NatOrder using (_≤_; z≤)
open import Agda.Builtin.Nat using (Nat; suc)

-- Exercise 10.15. Use the greedy loop only to obtain the minimum
-- width and one admissible numerator. Choose the nearest admissible
-- numerator at that width and render it, keeping leading zeroes.
extern : ∀ n → suc n ≤ 65536 → Σ (List Digit) (Closest n)
extern 0 _ = [] , winner zero-shortest (λ _ _ _ → z≤)
extern (suc t) bound = refine (Greedy.extern (suc t) bound)
  where refine : Σ (List Digit) (Shortest (suc t)) → Σ (List Digit) (Closest (suc t))
        refine (ds , ok) = Improve.solution t ds ok
