{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXDistanceScale where

open import AoP.Common.Prelude
open import AoP.Chapter03.TeXFraction using (Digit)
open import AoP.Chapter10.TeXExternal using (length)
open import AoP.Chapter10.TeXClosestShortest using (error; scale; numerator)
open import AoP.Chapter03.RoundingCollision using (suffix; seven; eight)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

-- At width k the decimal denominator is 10^k, including leading
-- zeroes. Consequently the distance scores for all the second-pass
-- candidates use exactly the same denominator, 65536 times that power.
power : Nat → Nat
power 0 = 1
power (suc k) = 10 * power k
width : ∀ ds → scale ds ≡ power (length ds)
width [] = refl
width (d ∷ ds) = cong (10 *_) (width ds)
common : ∀ ds es → length ds ≡ length es → 65536 * scale ds ≡ 65536 * scale es
common ds es eq = cong (65536 *_) (width ds ∙ cong power eq ∙ back (width es))
  where back : ∀ {a b : Nat} → a ≡ b → b ≡ a
        back refl = refl

-- The general score specializes to the two hand-calculated errors.
left-score : error 5 (suffix seven) ≡ 41248
left-score = refl
right-score : error 5 (suffix eight) ≡ 24288
right-score = refl
