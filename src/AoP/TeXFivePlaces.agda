{-# OPTIONS --safe --without-K #-}
module AoP.TeXFivePlaces where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; z≤; s≤; sum-mono; rid; chain)
open import AoP.OpenUpperDigit using (Upper)
open import AoP.TeXGridStop using (InCell)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- An interval at least one grid spacing wide contains its greatest
-- strict-upper numerator. Cancel the common spacing from both bounds.
private
  cancel : ∀ w {a b} → w + a ≤ w + b → a ≤ b
  cancel 0 p = p
  cancel (suc w) (s≤ p) = cancel w p

wide : ∀ w L H z → w + L ≤ H → Upper w H z → InCell w L H z
wide w L H z space (lo , hi) = cancel w (chain space hi) , lo

-- Factor the bound through smaller witnesses to avoid a long unary proof.
private
  pad : ∀ a b → a ≤ a + b
  pad 0 b = z≤
  pad (suc a) b = s≤ (pad a b)
  times : ∀ k {a b} → a ≤ b → k * a ≤ k * b
  times 0 h = z≤
  times (suc k) h = sum-mono h (times k h)

-- 200000 = 131072 + 68928.
room : 131072 ≤ 200000
room = pad 131072 68928

five : ∀ L z → Upper 131072 (200000 + L) z → InCell 131072 L (200000 + L) z
five L z = wide 131072 L (200000 + L) z (sum-mono {a = 131072} {b = 200000} {c = L} {d = L} room (rid L))
