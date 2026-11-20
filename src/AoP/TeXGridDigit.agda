{-# OPTIONS --safe --without-K #-}
module AoP.TeXGridDigit where

open import AoP.Prelude
open import AoP.OpenUpperDigit using (Upper)
open import AoP.FractionCrossOrder using (module Arithmetic)
open Arithmetic using (dist; switch; sym; move; swap)
open import AoP.NatOrder using (rid; sum-mono)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- Translate a local open-upper cell by any whole number of grid steps.

translate : ∀ w offset h d → Upper w h d → Upper w (offset * w + h) (offset + d)
translate w offset h d (lo , hi) rewrite dist offset d w | swap w (offset * w) (d * w) | sym (move (offset * w) (d * w)) =
  sum-mono (rid _) lo , sum-mono (rid _) hi

-- H = z*w + q is the old upper endpoint in global coordinates.
-- Append the digit chosen against the residual q. Multiplying the
-- old coordinates by ten turns the old prefix into offset z*10.
advance : ∀ w z q d → Upper w (q * 10) d → Upper w ((z * w + q) * 10) (z * 10 + d)
advance w z q d local rewrite dist (z * w) q 10 | switch z w 10 = translate w (z * 10) (q * 10) d local
