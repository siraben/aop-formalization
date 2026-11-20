{-# OPTIONS --safe --without-K #-}
module AoP.TeXExactState where

open import AoP.Prelude
open import AoP.TeXFraction using (Digit; cshift)
open import AoP.TeXReadCell using (state)
open import AoP.TeXClosestShortest using (scale; numerator)
open import AoP.TeXNestedCell using (translate; compose)
open import AoP.StrictUpperQuotient using (cell)
open import AoP.DigitInterval using (Cell)
open import AoP.FractionCrossOrder using (module Arithmetic)
open Arithmetic using (comm; dist; switch; sym)
open import AoP.NatOrder using (s≤; z≤)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

-- Fold invariant: state is the floor of W times the exact decimal.
-- Move W across place value only after composing the two floor cells.
private
  shift : ∀ w d v n → (w * d) * v + n * w ≡ (d * v + n) * w
  shift w d v n = cong (λ a → a * v + n * w) (comm w d) ∙ cong (_+ (n * w)) (switch d w v) ∙ sym (dist (d * v) n w)
  cast : ∀ v {x y} s → x ≡ y → Cell v x s → Cell v y s
  cast v s refl c = c
  layer : ∀ w d v n s t → Cell v (n * w) s → Cell 10 (w * d + s) t → Cell (10 * v) ((d * v + n) * w) t
  layer w d v n s t suffix digit = cast (10 * v) t (shift w d v n) (compose v 10 ((w * d) * v + n * w) (w * d + s) t (translate v (w * d) (n * w) s suffix) digit)

exact : ∀ ds → Cell (scale ds) (numerator ds * 131072) (state ds)
exact [] = z≤ , s≤ z≤
exact (d ∷ ds) = layer 131072 (Digit.numeral d) (scale ds) (numerator ds) (state ds) (cshift d (state ds)) (exact ds) (cell 9 (131072 * Digit.numeral d + state ds))
