{-# OPTIONS --safe --without-K #-}
module AoP.QuarterZero where

open import AoP.Prelude
open import AoP.QuarterCells using (Rounded)
open import AoP.NatOrder using (_≤_; z≤; s≤; rid; sum-mono)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- The zero cell has no lower test: decimal fractions are nonnegative.
-- Its strict upper endpoint 1/8 is excluded (the tie rounds upward).
private
  unit : ∀ d → d + 0 ≡ d
  unit 0 = refl
  unit (suc d) = cong suc (unit d)
  shift : ∀ d x → d + suc x ≡ suc (d + x)
  shift 0 x = refl
  shift (suc d) x = cong suc (shift d x)
  cancel : ∀ d {x y} → d + x ≤ d + y → x ≤ y
  cancel 0 p = p
  cancel (suc d) (s≤ p) = cancel d p

remove : ∀ a d → Rounded a d 0 → suc (8 * a) ≤ d
remove a d (lo , hi) with cancel d (align hi)
  where align : suc (d + 8 * a) ≤ d + (d + 0) → d + suc (8 * a) ≤ d + (d + 0)
        align p rewrite shift d (8 * a) = p
... | p rewrite unit d = p
restore : ∀ a d → suc (8 * a) ≤ d → Rounded a d 0
restore a d p = z≤ , align (sum-mono (rid d) p)
  where align : d + suc (8 * a) ≤ d + d → suc (d + 8 * a) ≤ d + (d + 0)
        align q rewrite unit d | shift d (8 * a) = q
