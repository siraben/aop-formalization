{-# OPTIONS --safe --without-K #-}
module AoP.TeXRoundInterval where

open import AoP.Prelude
open import AoP.TeXFraction using (Digit; intern)
open import AoP.TeXReadCell using (state; forward; backward)
open import AoP.TeXExactState using (exact)
open import AoP.TeXCellThreshold using (module At)
open import AoP.TeXClosestShortest using (scale; numerator)
open import AoP.TeXGridStop using (InCell)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

module Decimal (k : Nat) (ds : List Digit) where
  lo = suc (k * 2)
  hi = suc (suc lo)
  Valid = InCell 131072 (lo * scale ds) (hi * scale ds) (numerator ds)
  module T = At (scale ds) (numerator ds * 131072) (state ds) (exact ds)
  -- Exactly the half-open grid used by the printer, with no hypothesis
  -- about how the list was generated. Leading zeroes count in its scale.
  into : intern ds ≡ suc k → Valid
  into eq = T.lower lo (fst bounds) , T.upper hi (snd bounds)
    where bounds = forward k ds eq
  out : Valid → intern ds ≡ suc k
  out (a , b) = backward k ds (T.lower-back lo a , T.upper-back hi b)
