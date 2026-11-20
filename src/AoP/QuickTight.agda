{-# OPTIONS --safe --without-K #-}
module AoP.QuickTight where

open import AoP.Prelude
open import AoP.Quicksort using (unfold)
open import AoP.QuickSplitWork using (work)
open import AoP.QuickWorstBound using (bound)
open import AoP.QuickZeros using (zeros; exact)
open import AoP.SelectionSort using (length)
open import AoP.SelectionQuadratic using (double)
open import AoP.OrderedPairs using (pred)
open import AoP.NatOrder using (_≤_; sum-mono; rid)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- The worst case at each length is attained by an actual input to the
-- executable unfold. Doubling both sides avoids division by two.
comparisons : List Nat → Nat
comparisons xs = work (unfold (length xs) xs (rid _))
upper : ∀ xs → comparisons xs + comparisons xs ≤ length xs * pred (length xs)
upper xs with bound (unfold (length xs) xs (rid _))
... | le with sum-mono le le
...   | twice rewrite double (length xs) = twice

size : ∀ n → length (zeros n) ≡ n
size 0 = refl
size (suc n) = cong suc (size n)
attained : ∀ n → Σ (List Nat) λ xs → (length xs ≡ n) × (comparisons xs + comparisons xs ≡ n * pred n)
attained n = zeros n , size n , (cong (λ k → k + k) (exact n (length (zeros n)) (rid _)) ∙ double n)
