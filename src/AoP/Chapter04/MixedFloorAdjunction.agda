{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.MixedFloorAdjunction where

open import AoP.Common.Prelude
open import AoP.Chapter07.SignedSegment as Z using (pp; np; nn)
import AoP.Common.NatOrder as N
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Int using (Int; pos; negsuc)

-- Exercise 4.38 on the grid with denominator d+1. A point has
-- value z + r/(d+1), with 0 ≤ r ≤ d; z may be negative. Compare
-- whole parts first, and compare numerators when the whole parts tie.
module Grid (d : Nat) where
  record Point : Set where
    constructor point
    field whole : Int
          numerator : Nat
          bounded : numerator N.≤ d
  open Point
  _≼_ : Point → Point → Set
  x ≼ y = (whole x Z.≤ whole y) × (whole y Z.≤ whole x → numerator x N.≤ numerator y)
  reflexive : ∀ x → x ≼ x
  reflexive x = Z.rid _ , λ _ → N.rid _
  transitive : ∀ {x y z} → x ≼ y → y ≼ z → x ≼ z
  transitive (p , f) (q , g) = Z.chain p q , λ h → N.chain (f (Z.chain q h)) (g (Z.chain h p))
  embed : Int → Point
  embed z = point z 0 N.z≤
  lower : ∀ z x → embed z ≼ x → z Z.≤ whole x
  lower z x = fst
  upper : ∀ z x → z Z.≤ whole x → embed z ≼ x
  upper z x p = p , λ _ → N.z≤

-- -9/8 = -2 + 7/8. Its floor is -2, the right adjoint's value.
module Eighths = Grid 7
example : Eighths.Point.whole (Eighths.point (negsuc 1) 7 (N.rid 7)) ≡ negsuc 1
example = refl
