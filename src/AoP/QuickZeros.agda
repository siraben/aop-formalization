{-# OPTIONS --safe --without-K #-}
module AoP.QuickZeros where

open import AoP.Prelude
open import AoP.Quicksort
open import AoP.QuickSplitWork using (pass; work)
open import AoP.SelectionSort using (length)
open import AoP.SelectionTotalCost using (tri)
open import AoP.NatOrder using (_≤_; rid; z≤; s≤)
open import Agda.Builtin.Nat using (Nat; suc; _+_)

-- An arbitrarily long input of identical zeros. Every tie goes left,
-- so no pivot divides the remaining work between two nonempty children.
zeros : Nat → List Nat
zeros 0 = []
zeros (suc n) = 0 ∷ zeros n
trace : ∀ n → Split 0 (0 ∷ zeros n) (zeros n) []
trace 0 = pivot 0
trace (suc n) = left z≤ (trace n)
actual : ∀ n → split 0 (zeros n) ≡ (0 , zeros n , [] , trace n)
actual 0 = refl
actual (suc n) rewrite actual n = refl
count : ∀ n → pass (trace n) ≡ n
count 0 = refl
count (suc n) = cong suc (count n)
private
  unit : ∀ n → n + 0 ≡ n
  unit 0 = refl
  unit (suc n) = cong suc (unit n)

exact : ∀ n fuel (b : length (zeros n) ≤ fuel) → work (unfold fuel (zeros n) b) ≡ tri n
exact 0 fuel b = refl
exact (suc n) (suc fuel) (s≤ b) rewrite actual n with smaller (trace n)
... | s≤ lb , s≤ rb rewrite count n = cong (n +_) (unit _ ∙ exact n fuel _)
