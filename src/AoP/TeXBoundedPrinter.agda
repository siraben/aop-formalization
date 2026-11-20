{-# OPTIONS --safe --without-K #-}
module AoP.TeXBoundedPrinter where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; chain; weaken; rid)
open import AoP.FractionCrossOrder using (module Arithmetic)
open import AoP.TeXFraction using (Digit)
open import AoP.TeXExternal using (Shortest; zero-shortest)
open import AoP.TeXPrefixShortest using (module Positive)
open import AoP.TeXOccupiedPrefix using (module Print)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

-- The public input condition is just n < 65536. At n = t+1 its
-- upper numerator 2n+1 is below 2(t+2), hence at most 131072.
extern : ∀ n → suc n ≤ 65536 → Σ (List Digit) (Shortest n)
extern 0 _ = [] , zero-shortest
extern (suc t) within = P.digits , Positive.certified t upper
  where
  upper : suc (suc (suc (t * 2))) ≤ 131072
  upper = chain (weaken (rid _)) (Arithmetic.scale 2 {a = suc (suc t)} {b = 65536} within)
  module P = Print (suc (t * 2)) upper
