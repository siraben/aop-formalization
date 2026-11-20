{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.Bump where

open import AoP.Common.Prelude
open import AoP.Chapter02.Folds
open import AoP.Chapter05.Subsequences using (_∈_; here; there; Subseq)
open import AoP.Chapter04.Relations using (nil; cons)
open import AoP.Chapter05.Refinement using (skip; keep)
open import AoP.Chapter08.Thinning using (Thin; thin; thin-compose; thin-id)

-- §8.3 — Prune a list without reordering it. Imagine keeping candidate
-- routes: a cheaper route with the same origin dominates a dearer one,
-- but routes from different origins may be incomparable. Compare each
-- new candidate with the first survivor of the suffix. Drop the loser,
-- or keep both if neither dominates. This need not find the shortest
-- representation; it must keep a representative for every original entry.
module Prune {A : Set} (_≼_ : A → A → Set) (rid : ∀ x → x ≼ x)
             (chain : ∀ {x y z} → x ≼ y → y ≼ z → x ≼ z) where
  data Comparison (x y : A) : Set where
    first : x ≼ y → Comparison x y
    second : y ≼ x → Comparison x y
    retain : Comparison x y

  -- Keeping both is always sound, even if the test is conservative.
  module Algorithm (compare : ∀ x y → Comparison x y) where
    bump : A → List A → List A
    bump x [] = x ∷ []
    bump x (y ∷ ys) with compare x y
    ... | first _ = x ∷ ys
    ... | second _ = y ∷ ys
    ... | retain = x ∷ y ∷ ys

    thinlist = ⦅ [] ∣ bump ⦆

    Covers : List A → List A → Set
    Covers xs ys = Thin _≼_ (_∈ xs) (_∈ ys)

    lift : ∀ x {xs ys} → Covers xs ys → Covers (x ∷ xs) (x ∷ ys)
    Thin.subset (lift x t) here = here
    Thin.subset (lift x t) (there p) = there (Thin.subset t p)
    Thin.cover (lift x t) _ here = x , here , rid x
    Thin.cover (lift x t) a (there p) with Thin.cover t a p
    ... | b , q , le = b , there q , le

    local : ∀ x xs → Covers (bump x xs) (x ∷ xs)
    local x [] = thin-id rid
    local x (y ∷ ys) with compare x y
    ... | retain = thin-id rid
    ... | first le = thin (λ { here → here ; (there p) → there (there p) }) λ where
      _ here → x , here , rid x
      _ (there here) → x , here , le
      a (there (there p)) → a , there p , rid a
    ... | second le = thin there λ where
      _ here → y , here , le
      a (there p) → a , p , rid a

    correct : ∀ xs → Covers (thinlist xs) xs
    correct [] = thin-id rid
    correct (x ∷ xs) = thin-compose chain (local x (thinlist xs)) (lift x (correct xs))

    -- Coverage alone would permit shuffling or duplicating candidates.
    -- The second half of the specification is about their positions:
    -- each survivor must occupy a distinct input slot, in input order.
    drop-first : ∀ {y : A} {ys xs} → Subseq (y ∷ ys) xs → Subseq ys xs
    drop-first (cons keep p) = cons skip p
    drop-first (cons skip p) = cons skip (drop-first p)

    ordered : ∀ xs → Subseq (thinlist xs) xs
    ordered [] = nil refl
    ordered (x ∷ xs) with thinlist xs | ordered xs
    ... | [] | p = cons keep p
    ... | y ∷ ys | p with compare x y
    ...   | first le = cons keep (drop-first p)
    ...   | second le = cons skip p
    ...   | retain = cons keep p
