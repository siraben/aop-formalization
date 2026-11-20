{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.SuffixFold where

open import AoP.Common.Prelude
open import AoP.Chapter02.Folds
open import AoP.Chapter08.Paragraph using (Nonempty; _∷⁺_)
open import AoP.Chapter05.ZippedSplits using (tails)
private variable A : Set

-- §5.6. To compute descending suffixes by a cons-list fold, keep the
-- suffix collection nonempty. Its first entry is the entire suffix
-- processed so far. Prepend the next element to that entry alone, then
-- keep all old entries. For [] the one entry is the empty suffix.
extend : A → Nonempty (List A) → Nonempty (List A)
extend a (xs ∷⁺ rest) = (a ∷ xs) ∷⁺ (xs ∷ rest)

scan : List A → Nonempty (List A)
scan = ⦅ ([] ∷⁺ []) ∣ extend ⦆

entries : Nonempty (List A) → List (List A)
entries (x ∷⁺ xs) = x ∷ xs

-- The invariant exposes the current whole suffix, which is needed to
-- derive the fold step. The second component stores its proper suffixes.
proper : List A → List (List A)
proper [] = []
proper (_ ∷ xs) = tails xs

unroll : (xs : List A) → xs ∷ proper xs ≡ tails xs
unroll [] = refl
unroll (_ ∷ _) = refl

invariant : (xs : List A) → scan xs ≡ (xs ∷⁺ proper xs)
invariant [] = refl
invariant (a ∷ xs) = begin
  extend a (scan xs) ≡⟨ cong (extend a) (invariant xs) ⟩
  (a ∷ xs) ∷⁺ (xs ∷ proper xs) ≡⟨ cong ((a ∷ xs) ∷⁺_) (unroll xs) ⟩
  (a ∷ xs) ∷⁺ tails xs ∎

correct : (xs : List A) → entries (scan xs) ≡ tails xs
correct xs = cong entries (invariant xs) ∙ unroll xs
