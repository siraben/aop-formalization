{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXOccupiedPrefix where

open import AoP.Common.Prelude
open import AoP.Chapter10.TeXGridMinimum using (module Positive)
open import AoP.Chapter10.TeXFirstGrid using (Answer)
open import AoP.Chapter10.TeXPrefixRun using (module Run)
open import AoP.Chapter10.TeXClosestShortest using (numerator)
open import AoP.Chapter10.TeXGridStop using (InCell; module Grid)
open import AoP.Common.NatOrder using (_≤_; chain)
open import AoP.Chapter04.FractionCrossOrder using (module Arithmetic)
open import Agda.Builtin.Nat using (Nat; suc; _+_)

-- Run the digit transition to the first occupied width. Both searches
-- have the same upper endpoint there, so the emitted prefix dominates
-- the grid winner and, in particular, crosses the lower endpoint.
module Print (l : Nat) (bounded : 2 + l ≤ 131072) where
  module G = Positive l
  module R = Run 131071 (suc l) bounded
  open Answer G.optimum renaming (places to k; value to z)
  prefix = R.run k
  digits = R.Prefix.ds prefix
  p = numerator digits
  module Cut = Grid 131072 (G.L k) (G.H k) p (R.Prefix.greatest prefix)
  reaches : z ≤ p
  reaches = Cut.dominates z (snd fits)
  valid : InCell 131072 (G.L k) (G.H k) p
  valid = Cut.stop (chain (fst fits) (Arithmetic.scale 131072 reaches))
  agreement : p ≡ z
  agreement = anti (greatest p valid) reaches
    where anti : ∀ {x y} → x ≤ y → y ≤ x → x ≡ y
          anti AoP.Common.NatOrder.z≤ AoP.Common.NatOrder.z≤ = refl
          anti (AoP.Common.NatOrder.s≤ a) (AoP.Common.NatOrder.s≤ b) = cong suc (anti a b)
