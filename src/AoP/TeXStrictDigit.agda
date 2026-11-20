{-# OPTIONS --safe --without-K #-}
module AoP.TeXStrictDigit where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; z≤; s≤; chain; rid; sum-mono)
open import AoP.FractionCrossOrder using (module Arithmetic)
open import AoP.OpenUpperDigit using (Upper)
open import AoP.TeXFraction using (Digit; digit)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

-- The repaired open-endpoint rule remains a decimal-digit rule even
-- at residual q = w. In this case ordinary division would return 10.
private
  mono : ∀ w {a b} → a ≤ b → a * w ≤ b * w
  mono w z≤ = z≤
  mono w (s≤ p) = sum-mono (rid w) (mono w p)
  cancel : ∀ {a b} → suc a ≤ suc b → a ≤ b
  cancel (s≤ p) = p
  cast : ∀ {a b c} → b ≡ c → a ≤ b → a ≤ c
  cast refl p = p
  reflect : ∀ w a b → suc (a * w) ≤ b * w → suc a ≤ b
  reflect w a 0 ()
  reflect w 0 (suc b) _ = s≤ z≤
  reflect w (suc a) (suc b) p = s≤ (reflect w a b (strip w p))
    where strip : ∀ k {x y} → suc (Agda.Builtin.Nat._+_ k x) ≤ Agda.Builtin.Nat._+_ k y → suc x ≤ y
          strip 0 h = h
          strip (suc k) (s≤ h) = strip k h

legal : ∀ w q d → q ≤ w → Upper w (q * 10) d → d ≤ 9
legal w q d bound local = cancel (reflect w d 10 (chain (fst local) (cast (Arithmetic.comm w 10) (mono 10 bound))))
output : ∀ w q d → q ≤ w → Upper w (q * 10) d → Digit
output w q d p u = digit d (legal w q d p u)
