{-# OPTIONS --safe --without-K #-}
module AoP.TeXPrinterStep where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; s≤; z≤)
open import AoP.StrictUpperQuotient using (choose; strict)
open import AoP.TeXStrictDigit using (output)
open import AoP.TeXUpperResidual using (module Step)
open import AoP.TeXGridDigit using (advance)
open import AoP.TeXLowerResidual using (residual)
open import AoP.TeXFraction using (Digit)
open import AoP.OpenUpperDigit using (Upper)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_; _-_)

-- k and j denote predecessors, so neither the width nor the upper
-- residual can vanish. The module computes the digit and both updates
-- solely from integer state, with no cell certificate supplied by a caller.
module Emit (k j z p : Nat) (bounded : suc j ≤ suc k) where
  w = suc k
  q = suc j
  -- 10q - 1 = 9 + 10j, also at the exact-multiple endpoint.
  d = choose k (9 + j * 10)
  local : Upper w (q * 10) d
  local = strict k (9 + j * 10)
  letter : Digit
  letter = output w q d bounded local
  module Next = Step w z q d local
  new-prefix = z * 10 + Digit.numeral letter
  high = Next.residual
  low = p * 10 - d * w
  next-cell : Upper w ((z * w + q) * 10) new-prefix
  next-cell = advance w z q d local
  next-high : (1 ≤ high) × (high ≤ w)
  next-high = Next.positive-bound , Next.upper-bound
  exact : new-prefix * w + high ≡ (z * w + q) * 10
  exact = Next.reconstruct
  clipped : (z * w + p) * 10 - new-prefix * w ≡ low
  clipped = residual w z p d
