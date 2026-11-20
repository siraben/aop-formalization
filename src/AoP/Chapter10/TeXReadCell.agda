{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXReadCell where

open import AoP.Common.Prelude
open import AoP.Chapter10.DigitInterval using (Cell; unique)
open import AoP.Chapter10.StrictUpperQuotient using (cell)
open import AoP.Common.NatOrder using (_≤_; s≤)
open import AoP.Chapter03.TeXFraction using (Digit; intern; cshift; halve)
open import AoP.Chapter02.Folds using (⦅_∣_⦆)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

-- Characterize the actual final rounding in integer suffix-state units.
-- For target k+1 the two adjacent half-unit thresholds are 2k+1
-- (included) and 2k+3 (excluded). No decimal valuation is assumed here.
state : List Digit → Nat
state = ⦅ 0 ∣ cshift ⦆
Between : Nat → Nat → Set
Between k s = (suc (k * 2) ≤ s) × (suc s ≤ suc (suc (suc (k * 2))))

unpack : ∀ k s → Cell 2 (suc s) (suc k) → Between k s
unpack k s (s≤ lo , s≤ hi) = lo , hi

forward : ∀ k ds → intern ds ≡ suc k → Between k (state ds)
forward k ds eq = unpack k (state ds) (cast eq (cell 1 (suc (state ds))))
  where cast : ∀ {a b} → a ≡ b → Cell 2 (suc (state ds)) a → Cell 2 (suc (state ds)) b
        cast refl c = c

backward : ∀ k ds → Between k (state ds) → intern ds ≡ suc k
backward k ds (lo , hi) = unique 2 (suc (state ds)) (intern ds) (suc k) (cell 1 (suc (state ds))) (s≤ lo , s≤ hi)
