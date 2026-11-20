{-# OPTIONS --safe --without-K #-}
module AoP.SortedSubset where

open import AoP.Prelude
open import AoP.Relations using (_←_; nil; cons)
open import AoP.Refinement using (keep; skip)
open import AoP.Subsequences using (Subseq; _∈_)
open import AoP.OrderedMeet using (module Order)
open import AoP.ConnectedBlock using (module Law)
open import AoP.Thinning using (Pred)
open import AoP.Power using (_≐_)

-- Exercise 8.17. Given an ordered listing of X, retain any subsequence.
-- The smaller set witnessing the factorization is exactly the set of
-- members of that subsequence. Deletion preserves every required
-- pairwise comparison, even for a relation that is not connected.
module Sort {A : Set} (P : A ← A) where
  open Order {A} using (Ordered)
  Listing : List A → Pred A → Set
  Listing xs X = Ordered P xs × ((_∈ xs) ≐ X)

  ordered-sub : ∀ {xs ys} → Subseq xs ys → Ordered P ys → Ordered P xs
  ordered-sub (nil refl) Order.nil = Order.nil
  ordered-sub (cons skip s) (Order.cons _ rest) = ordered-sub s rest
  ordered-sub (cons keep s) (Order.cons lower rest) = Order.cons (λ m → lower (Law.member P s m)) (ordered-sub s rest)

  factor : ∀ {xs ys X} → Subseq xs ys → Listing ys X →
           Σ (Pred A) λ Y → Listing xs Y × (∀ a → Y a → X a)
  factor {xs} s (ord , to , from) = (_∈ xs) , (ordered-sub s ord , (λ _ m → m) , (λ _ m → m)) ,
                                     λ a m → to a (Law.member P s m)
