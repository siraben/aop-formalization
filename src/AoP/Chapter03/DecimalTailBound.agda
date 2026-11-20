{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.DecimalTailBound where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; sum-mono; rid; s≤; z≤)
open import AoP.Chapter03.QuarterDigits using (num; den)
open import AoP.Chapter03.TeXFraction using (Digit)
open import AoP.Chapter03.SeventeenGrid using (boundary; preserve)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- Exercise 3.17. A finite tail can approach one (.9, .99, ...)
-- but never reaches it. Its entire contribution in prefix-grid units
-- therefore occupies strictly less than one grid step.
private
  sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl
  scale : ∀ d {a b} → a ≤ b → a * d ≤ b * d
  scale d z≤ = z≤
  scale d (s≤ p) = sum-mono (rid d) (scale d p)
  shift : ∀ n m → n + suc m ≡ suc (n + m)
  shift 0 m = refl
  shift (suc n) m = cong suc (shift n m)
  unit : ∀ a → a + 0 ≡ a
  unit 0 = refl
  unit (suc a) = cong suc (unit a)
  commute : ∀ a b → a + b ≡ b + a
  commute 0 b = sym (unit b)
  commute (suc a) b = cong suc (commute a b) ∙ sym (shift b a)

proper : ∀ ds → suc (num ds) ≤ den ds
proper [] = rid 1
proper (h ∷ ds) rewrite sym (shift (Digit.numeral h * den ds) (num ds)) | commute (den ds) (9 * den ds) =
  sum-mono (scale (den ds) (Digit.valid h)) (proper ds)

threshold : ∀ j p ds →
  (boundary j * den ds ≤ p * den ds + num ds → boundary j ≤ p) ×
  (boundary j ≤ p → boundary j * den ds ≤ p * den ds + num ds)
threshold j p ds = preserve j p (den ds) (num ds) (proper ds)
