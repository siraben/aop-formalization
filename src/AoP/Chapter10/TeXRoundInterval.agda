{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXRoundInterval where

open import AoP.Common.Prelude
open import AoP.Chapter03.TeXFraction using (Digit; intern)
open import AoP.Chapter10.TeXReadCell using (state; forward; backward)
open import AoP.Chapter10.TeXExactState using (exact)
open import AoP.Chapter10.TeXCellThreshold using (module At)
open import AoP.Chapter10.TeXClosestShortest using (scale; numerator)
open import AoP.Chapter10.TeXGridStop using (InCell)
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
