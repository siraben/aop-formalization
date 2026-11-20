{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.ReverseAccumulator where

open import AoP.Common.Prelude
open import AoP.Chapter01.Naturality using (_++_; reverse)
private variable A : Set

-- Exercise 3.47. The specification appends a singleton after each
-- recursive reversal. Generalize the result to reverse xs ++ suffix:
-- associativity turns that append into a cons on the incoming suffix.
run : List A → List A → List A
run [] suffix = suffix
run (x ∷ xs) suffix = run xs (x ∷ suffix)

private
  assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  assoc [] ys zs = refl
  assoc (x ∷ xs) ys zs = cong (x ∷_) (assoc xs ys zs)
  right-unit : (xs : List A) → xs ≡ xs ++ []
  right-unit [] = refl
  right-unit (x ∷ xs) = cong (x ∷_) (right-unit xs)

invariant : (xs suffix : List A) → reverse xs ++ suffix ≡ run xs suffix
invariant [] suffix = refl
invariant (x ∷ xs) suffix = begin
  (reverse xs ++ (x ∷ [])) ++ suffix ≡⟨ assoc (reverse xs) (x ∷ []) suffix ⟩
  reverse xs ++ (x ∷ suffix) ≡⟨ invariant xs (x ∷ suffix) ⟩
  run (x ∷ xs) suffix ∎

correct : (xs : List A) → reverse xs ≡ run xs []
correct xs = right-unit (reverse xs) ∙ invariant xs []
