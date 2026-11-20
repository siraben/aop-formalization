{-# OPTIONS --safe --without-K #-}
module AoP.TeXFraction where

open import AoP.Prelude
open import AoP.Folds
open import AoP.NatOrder using (_≤_; z≤)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_; div-helper)

-- §3.3 — TeX stores a length in units of 1/65536. For a decimal
-- fraction 0.d₁…dₖ, return the nearest number of units, rounding ties
-- upward. The tempting strategy of rounding each suffix too soon loses
-- information. Keep one extra binary digit throughout the fold and
-- round only once, after the most significant decimal digit is handled.
record Digit : Set where
  constructor digit
  field numeral : Nat; valid : numeral ≤ 9
open Digit

-- div-helper 0 k n k computes n div (1+k), with a positive divisor.
cshift : Digit → Nat → Nat
cshift d n = div-helper 0 9 (131072 * numeral d + n) 9

halve : Nat → Nat
halve n = div-helper 0 1 (suc n) 1

intern : List Digit → Nat
intern ds = halve (⦅ 0 ∣ cshift ⦆ ds)

-- Why not fuse halve into the digit fold too? With incoming digit zero,
-- suffix states 9 and 10 have the same rounded value (5). Yet after
-- shifting, they round to 0 and 1. No step on the rounded state alone
-- can satisfy the second fusion equation for all intermediate states.
no-second-fusion : (f : Digit → Nat → Nat) →
                   (∀ d n → halve (cshift d n) ≡ f d (halve n)) → ⊥
no-second-fusion f law = distinct contradiction
  where
  d = digit 0 z≤
  back : ∀ {a b : Nat} → a ≡ b → b ≡ a
  back refl = refl
  contradiction : 0 ≡ 1
  contradiction = begin
    halve (cshift d 9)  ≡⟨ law d 9 ⟩
    f d 5               ≡⟨ back (law d 10) ⟩
    halve (cshift d 10) ∎
  distinct : 0 ≡ 1 → ⊥
  distinct ()

-- Factor out the arithmetic floor lemma from the structural calculation:
-- for an exact interpretation V, scaled v is floor(131072 * v).
-- Its commuting square below is the rule of floors applied to (d+v)/10.
-- The theorem proves the fusion step, not that arithmetic lemma itself.
module Derivation (V : Set) (zero : V) (shift : Digit → V → V) (scaled : V → Nat)
                  (at-zero : scaled zero ≡ 0)
                  (floor-shift : ∀ d v → scaled (shift d v) ≡ cshift d (scaled v)) where
  val : List Digit → V
  val = ⦅ zero ∣ shift ⦆

  calculation : ∀ ds → halve (scaled (val ds)) ≡ intern ds
  calculation ds = begin
    halve (scaled (val ds))                ≡⟨ cong halve (fusion scaled zero shift cshift floor-shift ds) ⟩
    halve (⦅ scaled zero ∣ cshift ⦆ ds)    ≡⟨ cong (λ z → halve (⦅ z ∣ cshift ⦆ ds)) at-zero ⟩
    intern ds ∎
