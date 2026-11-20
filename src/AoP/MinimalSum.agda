{-# OPTIONS --safe --without-K #-}
module AoP.MinimalSum where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.RelationalSums using (_⊕_; left; right)
open import AoP.MinimalComparison using (Test)
open import AoP.Thinning using (Min)

-- Exercise 7.24. Split the input set by tag. An incoming edge
-- preserves that tag, so minimality only inspects the same summand.
module Law {A B : Set} (R : A ← A) (S : B ← B) (X : A ⊎ B → Set) where
  Pieces : A ⊎ B → Set
  Pieces (inl a) = Min (Test R) a (λ x → X (inl x))
  Pieces (inr b) = Min (Test S) b (λ y → X (inr y))

  combine : ∀ z → Pieces z → Min (Test (R ⊕ S)) z X
  combine (inl a) (xa , check) = xa , λ { _ x (left p) → left (check _ x p) }
  combine (inr b) (xb , check) = xb , λ { _ x (right p) → right (check _ x p) }

  separate : ∀ z → Min (Test (R ⊕ S)) z X → Pieces z
  separate (inl a) (xa , check) = xa , λ x m p → unleft (check (inl x) m (left p))
    where unleft : ∀ {u v} → (R ⊕ S) (inl u) (inl v) → R u v
          unleft (left r) = r
  separate (inr b) (xb , check) = xb , λ y m p → unright (check (inr y) m (right p))
    where unright : ∀ {u v} → (R ⊕ S) (inr u) (inr v) → S u v
          unright (right s) = s
