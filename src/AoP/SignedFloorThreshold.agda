{-# OPTIONS --safe --without-K #-}
module AoP.SignedFloorThreshold where

open import AoP.Prelude
open import AoP.Complement using (⊥)
open import AoP.FractionThreshold using (strip; insert)
open import AoP.NatOrder using (_≤_; s≤; z≤)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- Exercise 3.19. Represent an integer by a difference of naturals.
-- In k ≤ (a+n+r/d)/b, move all negative terms to the opposite side
-- before clearing d. The fractional remainder occurs on the right
-- only, so the same denominator-block lemma applies for signed a,n,k.
record Difference : Set where
  constructor diff
  field plus minus : Nat
open Difference

module Test (a n k : Difference) (b′ d r : Nat) (small : suc r ≤ d) where
  b = suc b′
  left  = b * plus k + (minus a + minus n)
  right = b * minus k + (plus a + plus n)
  Fractional = left * d ≤ right * d + r
  Integral = left ≤ right
  remove : Fractional → Integral
  remove = strip left right d r small
  restore : Integral → Fractional
  restore = insert left right d r

-- (-1 + (-2 + 3/4))/2 = -9/8 meets threshold -2, but not -1.
module Example where
  module Yes = Test (diff 0 1) (diff 0 2) (diff 0 2) 1 4 3 (s≤ (s≤ (s≤ (s≤ z≤))))
  module No = Test (diff 0 1) (diff 0 2) (diff 0 1) 1 4 3 (s≤ (s≤ (s≤ (s≤ z≤))))
  lower : Yes.Fractional
  lower = Yes.restore (s≤ (s≤ (s≤ z≤)))
  higher : No.Fractional → ⊥
  higher p with No.remove p
  ... | s≤ (s≤ ())
