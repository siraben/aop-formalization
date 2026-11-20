{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.QuarterDigits where

open import AoP.Common.Prelude
open import AoP.Chapter03.TeXFraction using (Digit; digit)
open import AoP.Common.NatOrder using (_≤_; rid; z≤; s≤; sum-mono)
open import AoP.Chapter03.QuarterCells using (Rounded; Interval; remove; restore)
import AoP.Chapter03.QuarterZero as Zero
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- The value of a string of k digits is its place-value numerator over
-- 10^k. Prepending h adds h copies of the suffix denominator to the
-- numerator, and multiplies the denominator by ten (even for h = 0).
den : List Digit → Nat
den [] = 1
den (_ ∷ ds) = 10 * den ds
num : List Digit → Nat
num [] = 0
num (h ∷ ds) = Digit.numeral h * den ds + num ds

Cell : List Digit → Nat → Set
Cell ds = Rounded (num ds) (den ds)
positive : ∀ ds k → (Cell ds (suc k) → Interval (num ds) (den ds) k) ×
                    (Interval (num ds) (den ds) k → Cell ds (suc k))
positive ds k = remove (num ds) (den ds) k , restore (num ds) (den ds) k
zero : ∀ ds → (Cell ds 0 → suc (8 * num ds) ≤ den ds) ×
              (suc (8 * num ds) ≤ den ds → Cell ds 0)
zero ds = Zero.remove (num ds) (den ds) , Zero.restore (num ds) (den ds)

-- The string .125 denotes exactly 125/1000, the first midpoint.
mid : List Digit
mid = digit 1 (s≤ z≤) ∷ digit 2 (s≤ (s≤ z≤)) ∷ digit 5 (s≤ (s≤ (s≤ (s≤ (s≤ z≤))))) ∷ []
ratio : List Digit → Nat × Nat
ratio ds = num ds , den ds
value : ratio mid ≡ (125 , 1000)
value = refl
