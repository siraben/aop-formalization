{-# OPTIONS --safe --without-K #-}
module AoP.TeXEmitNumerator where

open import AoP.Prelude
open import AoP.TeXFraction using (Digit)
open import AoP.TeXClosestShortest using (scale; numerator)
open import AoP.TeXExternal using (length)
open import AoP.FractionCrossOrder using (module Arithmetic)
open Arithmetic using (dist; assoc; sym; unit; step; nil)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- The printer builds digits at the right, whereas the decoder's exact
-- valuation consumes them at the left. Relate these two orientations.
append : List Digit → Digit → List Digit
append [] d = d ∷ []
append (a ∷ ds) d = a ∷ append ds d
places : ∀ ds d → length (append ds d) ≡ suc (length ds)
places [] d = refl
places (a ∷ ds) d = cong suc (places ds d)
private
  times : ∀ a b c → a * (b * c) ≡ (a * b) * c
  times 0 b c = refl
  times (suc a) b c rewrite dist b (a * b) c | times a b c = refl
width : ∀ ds d → scale (append ds d) ≡ scale ds * 10
width [] d = refl
width (a ∷ ds) d = cong (10 *_) (width ds d) ∙ times 10 (scale ds) 10
value : ∀ ds d → numerator (append ds d) ≡ numerator ds * 10 + Digit.numeral d
value [] d = unit (Digit.numeral d * 1) ∙ step (Digit.numeral d) 0 ∙ cong (Digit.numeral d +_) (nil (Digit.numeral d)) ∙ unit (Digit.numeral d)
value (a ∷ ds) d rewrite width ds d | value ds d | times (Digit.numeral a) (scale ds) 10 | dist (Digit.numeral a * scale ds) (numerator ds) 10 = sym (assoc ((Digit.numeral a * scale ds) * 10) (numerator ds * 10) (Digit.numeral d))
