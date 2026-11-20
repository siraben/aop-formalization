{-# OPTIONS --safe --without-K #-}
module AoP.Chapter01.ConversionFold where

open import AoP.Common.Prelude
open import AoP.Chapter01.Snoc using (Snoc; ε; _▻_; foldl; prepend)
open import AoP.Chapter01.Naturality using (_++_)
private variable A : Set

-- Exercises 1.7–1.8. Appending a singleton to the converted prefix
-- traverses that prefix again. Fold into a function of the suffix so
-- that the snoc step becomes one cons instead.
convert : Snoc A → List A
convert = foldl [] (λ prefix x → prefix ++ (x ∷ []))

catconv : Snoc A → List A → List A
catconv = foldl (λ suffix → suffix) (λ k x suffix → k (x ∷ suffix))

private
  assoc : (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  assoc [] ys zs = refl
  assoc (x ∷ xs) ys zs = cong (x ∷_) (assoc xs ys zs)

spec : (xs : Snoc A) (ys : List A) → convert xs ++ ys ≡ catconv xs ys
spec ε ys = refl
spec (xs ▻ x) ys = begin
  (convert xs ++ (x ∷ [])) ++ ys ≡⟨ assoc (convert xs) (x ∷ []) ys ⟩
  convert xs ++ (x ∷ ys)         ≡⟨ spec xs (x ∷ ys) ⟩
  catconv xs (x ∷ ys) ∎

accumulator : (xs : Snoc A) (ys : List A) → catconv xs ys ≡ prepend xs ys
accumulator ε ys = refl
accumulator (xs ▻ x) ys = accumulator xs (x ∷ ys)
