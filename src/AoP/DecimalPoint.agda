{-# OPTIONS --safe --without-K #-}
module AoP.DecimalPoint where

open import AoP.Prelude
open import AoP.DecimalDigits using (Digit; oh; nonzero; one; two; three; four; five; value)
open import AoP.Snoc using (Snoc; foldl; ε; _▻_)
open import AoP.Folds using (⦅_∣_⦆)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

-- §1.3. Read 12.305 as a whole part 12 and a fraction 305/1000.
-- Digits before the point arrive by snoc: append d by shifting the
-- accumulated whole part left one decimal place. Digits after the point
-- arrive by cons: prepend e to n/q by forming (e*q+n)/(10*q).
whole : Snoc Digit → Nat
whole = foldl 0 (λ w d → 10 * w + value d)

record Ratio : Set where
  constructor _over_
  field numerator denominator : Nat

frac-step : Digit → Ratio → Ratio
frac-step e (n over q) = (value e * q + n) over (10 * q)

fraction : List Digit → Ratio
fraction = ⦅ (0 over 1) ∣ frac-step ⦆

eval : Snoc Digit → List Digit → Ratio
eval w ds with fraction ds
... | n over q = (whole w * q + n) over q

-- Retain the input precision. Three fractional places have denominator
-- 1000, including when one or more of those places carry a zero.
scale : List Digit → Nat
scale [] = 1
scale (_ ∷ ds) = 10 * scale ds

places : ∀ ds → Ratio.denominator (fraction ds) ≡ scale ds
places [] = refl
places (d ∷ ds) = cong (10 *_) (places ds)

example : eval ((ε ▻ nonzero one) ▻ nonzero two) (nonzero three ∷ oh ∷ nonzero five ∷ []) ≡ (12305 over 1000)
example = begin
  eval ((ε ▻ nonzero one) ▻ nonzero two) (nonzero three ∷ oh ∷ nonzero five ∷ [])
    ≡⟨⟩ -- Whole: shift 1 left one place, then add 2.
  ((10 * 1 + 2) * 1000 + Ratio.numerator (frac-step (nonzero three) (frac-step oh (frac-step (nonzero five) (0 over 1))))) over 1000
    ≡⟨⟩ -- Innermost digit: .5 is 5/10.
  (12 * 1000 + Ratio.numerator (frac-step (nonzero three) (frac-step oh (5 over 10)))) over 1000
    ≡⟨⟩ -- Prepending zero changes the scale: .05 is 5/100.
  (12 * 1000 + Ratio.numerator (frac-step (nonzero three) (5 over 100))) over 1000
    ≡⟨⟩ -- The leading 3 contributes 300 at scale 1000.
  (12 * 1000 + (3 * 100 + 5)) over 1000
    ≡⟨⟩
  12305 over 1000 ∎
