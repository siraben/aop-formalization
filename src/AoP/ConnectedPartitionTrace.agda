{-# OPTIONS --safe --without-K #-}
module AoP.ConnectedPartitionTrace where

open import AoP.Prelude
open import AoP.ParagraphMinimum using (Dec)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.ConnectedPartitionMinimum using (module Solver)
open import AoP.ConnectedPartitionThin using (module Select)

-- A common lower bound cannot connect two incomparable points in a
-- pairwise-connected block. The greedy prefix must end before right.
data Point : Set where low left right : Point
data _≤_ : Point → Point → Set where
  same : ∀ {x} → x ≤ x
  bottom : ∀ {x} → low ≤ x
trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
trans same b = b
trans bottom b = bottom
cmp : ∀ x y → Dec ((x ≤ y) ⊎ (y ≤ x))
cmp low y = inl (inl bottom)
cmp left low = inl (inr bottom)
cmp right low = inl (inr bottom)
cmp left left = inl (inl same)
cmp right right = inl (inl same)
cmp left right = inr λ { (inl ()) ; (inr ()) }
cmp right left = inr λ { (inl ()) ; (inr ()) }
module P = Solver _≤_ (λ _ → same) cmp
module T = Select _≤_ (λ _ → same) trans cmp
input = left ∷ low ∷ right ∷ []
blocks : P.block-list (P.Result.partition (P.solve input)) ≡ (left ∷ low ∷ []) ∷ (right ∷ []) ∷ []
blocks = refl
min-count : P.Result.count (P.solve input) ≡ 2
min-count = refl
selected : fst (T.thinlist input) ≡ low ∷ right ∷ []
selected = refl
