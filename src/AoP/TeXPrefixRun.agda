{-# OPTIONS --safe --without-K #-}
module AoP.TeXPrefixRun where

open import AoP.Prelude
import AoP.FractionCrossOrder
open import AoP.NatOrder using (_≤_; s≤; z≤)
open import AoP.TeXIntervalGrowth using (scale)
open import AoP.TeXClosestShortest using (numerator)
open import AoP.TeXExternal using (length)
open import AoP.TeXEmitNumerator using (append; value; places)
open import AoP.TeXPrinterStep using (module Emit)
open import AoP.OpenUpperDigit using (Upper)
open import AoP.TeXFraction using (Digit)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- Generate the successive prefixes of the upper-endpoint printer.
-- Stopping is a separate decision on the lower endpoint. The record
-- remembers the exact digits; the integer prefix is their valuation.
module Run (k j : Nat) (bound : suc j ≤ suc k) where
  w = suc k
  H = scale
  record Prefix (n : Nat) : Set where
    constructor prefix
    field ds : List Digit
          width : length ds ≡ n
          pred : Nat
          small : suc pred ≤ w
          endpoint : numerator ds * w + suc pred ≡ H n (suc j)
          greatest : Upper w (H n (suc j)) (numerator ds)
  open Prefix
  zero : Prefix 0
  zero = prefix [] refl j bound refl (s≤ z≤ , limit)
    where limit : suc j ≤ w + 0
          limit rewrite AoP.FractionCrossOrder.Arithmetic.unit w = bound
  next : ∀ {n} → Prefix n → Prefix (suc n)
  next {n} old = pack E.high (E.next-high) E.exact
    where
    module E = Emit k (pred old) (numerator (ds old)) 0 (small old)
    new = append (ds old) E.letter
    eq = value (ds old) E.letter
    pack : ∀ r → (1 ≤ r) × (r ≤ w) → E.new-prefix * w + r ≡ (numerator (ds old) * w + suc (pred old)) * 10 → Prefix (suc n)
    pack (suc r) (_ , b) h = prefix new (places (ds old) E.letter ∙ cong suc (width old)) r b end cell
      where end = cong (λ z → z * w + suc r) eq ∙ h ∙ cong (_* 10) (endpoint old)
            transport : ∀ {u v x y} → u ≡ v → x ≡ y → Upper w u x → Upper w v y
            transport refl refl p = p
            back : ∀ {x y : Nat} → x ≡ y → y ≡ x
            back refl = refl
            cell = transport (cong (_* 10) (endpoint old)) (back eq) E.next-cell
  run : ∀ n → Prefix n
  run 0 = zero
  run (suc n) = next (run n)
