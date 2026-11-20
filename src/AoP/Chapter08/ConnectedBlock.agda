{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.ConnectedBlock where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Relations using (nil; cons)
open import AoP.Chapter05.Refinement using (keep; skip)
open import AoP.Chapter05.Subsequences using (_∈_; here; there; Subseq)

-- Exercise 8.14. A block is connected when each pair of its entries
-- is comparable. Removing arbitrary occurrences cannot create an
-- incomparable pair. In particular a prefix remains connected, the
-- closure property needed by longest-prefix greedy partitioning.
module Law {A : Set} (Q : A → A → Set) where
  Connected : List A → Set
  Connected xs = ∀ a b → a ∈ xs → b ∈ xs → Q a b ⊎ Q b a

  member : ∀ {xs ys : List A} {a} → Subseq xs ys → a ∈ xs → a ∈ ys
  member (nil refl) ()
  member (cons skip sub) m = there (member sub m)
  member (cons keep sub) here = here
  member (cons keep sub) (there m) = there (member sub m)

  closed : ∀ {xs ys} → Subseq xs ys → Connected ys → Connected xs
  closed sub c a b ma mb = c a b (member sub ma) (member sub mb)

  -- To extend an already connected suffix on the left, only compare
  -- its entries with the newcomer. All old pairs keep their evidence.
  extend : ∀ {a xs} → Q a a → (∀ b → b ∈ xs → Q a b ⊎ Q b a) → Connected xs → Connected (a ∷ xs)
  extend self cross c _ _ here here = inl self
  extend self cross c _ b here (there m) = cross b m
  extend self cross c a _ (there m) here with cross a m
  ... | inl ba = inr ba
  ... | inr ab = inl ab
  extend self cross c a b (there m) (there n) = c a b m n
