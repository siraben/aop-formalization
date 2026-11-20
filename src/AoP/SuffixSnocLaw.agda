{-# OPTIONS --safe --without-K #-}
module AoP.SuffixSnocLaw where

open import AoP.Prelude
open import AoP.Naturality using (_++_)
open import AoP.Horner using (map)
open import AoP.ZippedSplits using (tails)
private variable A : Set

-- §5.6. Before the cons-list implementation, the book specifies
-- suffixes by adjoining a last element. All old suffixes acquire that
-- last element; the new empty suffix comes last. Recover this equation
-- from the cons recurrence, including the singleton and empty cases.
snoc : List A → A → List A
snoc xs a = xs ++ (a ∷ [])

last-step : (xs : List A) (a : A) → tails (snoc xs a) ≡ map (λ ys → snoc ys a) (tails xs) ++ ([] ∷ [])
last-step [] a = refl
last-step (x ∷ xs) a = begin
  tails (snoc (x ∷ xs) a) ≡⟨⟩
  snoc (x ∷ xs) a ∷ tails (snoc xs a) ≡⟨ cong (snoc (x ∷ xs) a ∷_) (last-step xs a) ⟩
  map (λ ys → snoc ys a) (tails (x ∷ xs)) ++ ([] ∷ []) ∎
