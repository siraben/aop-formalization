{-# OPTIONS --safe --without-K #-}
module AoP.SeventeenGrid where

open import AoP.Prelude
open import AoP.FractionThreshold using (strip; insert)
open import AoP.NatOrder using (_≤_)
open import Agda.Builtin.Nat using (Nat; suc; _*_; _+_)

-- Exercise 3.17. In TeX's half-up rule, the boundary between output
-- j and j+1 is (2j+1)/131072. Multiplying by 10^17 gives the integer
-- grid coordinate (2j+1)*5^17. Work in these grid coordinates so that
-- no proper fractional tail can cross a boundary.
power : Nat → Nat → Nat
power b 0 = 1
power b (suc k) = b * power b k
factor : power 10 17 ≡ 131072 * power 5 17
factor = refl
boundary : Nat → Nat
boundary j = (2 * j + 1) * power 5 17

-- p is the integer represented by the first seventeen digits, padded
-- on the right with zeros if needed. The full coordinate is p + r/d.
-- At a tie, the non-strict threshold test succeeds for both inputs.
preserve : ∀ j p d r → suc r ≤ d →
           (boundary j * d ≤ p * d + r → boundary j ≤ p) ×
           (boundary j ≤ p → boundary j * d ≤ p * d + r)
preserve j p d r small = strip (boundary j) p d r small , insert (boundary j) p d r
