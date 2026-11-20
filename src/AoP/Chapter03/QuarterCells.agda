{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.QuarterCells where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; s≤; z≤; rid; weaken; sum-mono)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- Exercise 3.16. For a decimal value a/d, rounding four times that
-- value half-up means taking floor((8a+d)/(2d)). Describe its cell
-- without division: each positive result k+1 occupies the interval
-- [(2k+1)/8,(2k+3)/8). Exact midpoint ties go to the larger result.
private
  cancel : ∀ d {x y} → d + x ≤ d + y → x ≤ y
  cancel 0 p = p
  cancel (suc d) (s≤ p) = cancel d p
  shift : ∀ d x → d + suc x ≡ suc (d + x)
  shift 0 x = refl
  shift (suc d) x = cong suc (shift d x)

even : Nat → Nat → Nat
even 0 d = 0
even (suc k) d = d + (d + even k d)
odd : Nat → Nat → Nat
odd k d = d + even k d

Rounded : Nat → Nat → Nat → Set
Rounded a d k = (even k d ≤ d + 8 * a) × (suc (d + 8 * a) ≤ even (suc k) d)
Interval : Nat → Nat → Nat → Set
Interval a d k = (odd k d ≤ 8 * a) × (suc (8 * a) ≤ odd (suc k) d)

remove : ∀ a d k → Rounded a d (suc k) → Interval a d k
remove a d k (lo , hi) = cancel d lo , cancel d (align hi)
  where align : suc (d + 8 * a) ≤ even (suc (suc k)) d → d + suc (8 * a) ≤ even (suc (suc k)) d
        align p rewrite shift d (8 * a) = p
restore : ∀ a d k → Interval a d k → Rounded a d (suc k)
restore a d k (lo , hi) = sum-mono (rid d) lo , align (sum-mono (rid d) hi)
  where align : d + suc (8 * a) ≤ even (suc (suc k)) d → suc (d + 8 * a) ≤ even (suc (suc k)) d
        align p rewrite shift d (8 * a) = p
