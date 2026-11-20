{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.FloorCounterexample where

open import AoP.Common.Prelude
open import Agda.Builtin.Nat using (Nat; suc; _+_; div-helper)

-- Exercise 3.20. Half-integers suffice to witness both failures. Inputs
-- A, R, B denote twice the actual a, r, b. The common factor of two
-- cancels in (a+r)/b. Taking the floor of r first replaces R by the
-- greatest even numerator below or equal to R.
module Test (A R d : Nat) where
  -- B = suc d ensures a strictly positive divisor.
  quotient : Nat → Nat
  quotient n = div-helper 0 d n d
  original = quotient (A + R)
  half = div-helper 0 1 R 1
  rounded = quotient (A + (half + half))

-- a=1/2, r=1/2, b=1: their sum crosses 1, while a+floor(r) does not.
module Offset = Test 1 1 1
fractional-offset : (Offset.original ≡ 1) × (Offset.rounded ≡ 0)
fractional-offset = refl , refl

-- a=0, r=3/2, b=3/2: r/b=1 but floor(r)/b=2/3.
module Divisor = Test 0 3 2
fractional-divisor : (Divisor.original ≡ 1) × (Divisor.rounded ≡ 0)
fractional-divisor = refl , refl
