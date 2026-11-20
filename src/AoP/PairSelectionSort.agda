{-# OPTIONS --safe --without-K #-}
module AoP.PairSelectionSort where

open import AoP.Prelude
open import AoP.SelectionPairFold using (select; correct)
open import AoP.SelectionSort using (length; remaining; perm-bound; Sorted; nil; cons; Result)
open import AoP.Permutations using (Perm; Insert; insert; empty; front; later)
open import AoP.QuickPermutation using (compose)
open import AoP.QuickOrdered using (convert)
open import AoP.NatOrder using (_≤_; s≤; rid)
open import Agda.Builtin.Nat using (Nat; suc)

-- Unfold the book's selector. Reconstructing its remainder can change
-- the order of the tail, but preserves its length and its occurrences.
private
  growth : ∀ {a xs ys} → Insert a xs ys → suc (length xs) ≡ length ys
  growth front = refl
  growth (later i) = cong suc (growth i)
  size : ∀ {xs ys} → Perm xs ys → length xs ≡ length ys
  size empty = refl
  size (insert p i) = cong suc (size p) ∙ growth i

run : ∀ n xs → length xs ≤ n → Σ (List Nat) λ ys → Perm xs ys × Sorted ys
run n [] _ = [] , empty , nil
run (suc n) (x ∷ xs) (s≤ le) with select x xs | correct x xs
... | k , rs | perm , bound with run n rs (remaining (size perm) le)
... | zs , p , sorted = (k ∷ zs) , compose perm (insert p front) , cons (perm-bound (convert p) bound) sorted

certified : ∀ xs → Result xs
certified xs with run (length xs) xs (rid _)
... | ys , p , ordered = ys , convert p , ordered

example : fst (certified (0 ∷ 2 ∷ 1 ∷ [])) ≡ 0 ∷ 1 ∷ 2 ∷ []
example = refl
