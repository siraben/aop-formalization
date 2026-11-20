{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.SortedFilter where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; nil; cons)
open import AoP.Chapter05.Refinement using (skip; keep)
open import AoP.Chapter05.Subsequences using (Subseq; _∈_; here; there)
open import AoP.Chapter08.SortedSubset using (module Sort)
open import AoP.Chapter07.FilterGreedy using (module Law)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter08.Thinning using (Pred)

-- Exercise 8.18, equation 8.9. Filter an ordered listing by a
-- decidable predicate. Surviving comparisons remain in their original
-- order, and the listed set becomes its intersection with the test.
module Restrict {A : Set} (P : A ← A) (T : Pred A) (test : ∀ a → T a ⊎ (T a → ⊥)) where
  open Law T test using (filter)
  open Sort P
  sub : ∀ xs → Subseq (filter xs) xs
  sub [] = nil refl
  sub (a ∷ xs) with test a
  ... | inl _ = cons keep (sub xs)
  ... | inr _ = cons skip (sub xs)

  sound : ∀ xs a → a ∈ filter xs → (a ∈ xs) × T a
  sound (x ∷ xs) a m with test x
  ... | inr _ with sound xs a m
  ...   | p , t = there p , t
  sound (x ∷ xs) a m | inl tx with m
  ... | here = here , tx
  ... | there q with sound xs a q
  ...   | p , t = there p , t

  complete : ∀ xs a → a ∈ xs → T a → a ∈ filter xs
  complete (x ∷ xs) .x here t with test x
  ... | inl _ = here
  ... | inr no with no t
  ...   | ()
  complete (x ∷ xs) a (there m) t with test x
  ... | inl _ = there (complete xs a m t)
  ... | inr _ = complete xs a m t

  restrict : ∀ xs X → Listing xs X → Listing (filter xs) (λ a → X a × T a)
  restrict xs X (ord , to , from) = ordered-sub (sub xs) ord , forward , backward
    where forward : ∀ a → a ∈ filter xs → X a × T a
          forward a m with sound xs a m
          ... | p , t = to a p , t
          backward : ∀ a → X a × T a → a ∈ filter xs
          backward a (x , t) = complete xs a (from a x) t
