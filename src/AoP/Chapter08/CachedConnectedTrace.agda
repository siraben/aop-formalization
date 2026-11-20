{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.CachedConnectedTrace where

open import AoP.Common.Prelude
open import AoP.Chapter01.Snoc using (ε; _▻_)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter08.ConnectedPartitionTrace using (Point; low; left; right; _≤_; same; bottom; trans; cmp)
open import AoP.Chapter08.CachedConnectedFold using (module Fold)

-- Each upper cone tested here has a linearly ordered set of lower
-- bounds: either one lower bound is low, or it is the upper point.
fork : ∀ {a b c} → a ≤ c → b ≤ c → a ≤ b ⊎ b ≤ a
fork same bc = inr bc
fork bottom bc = inl bottom
open Fold _≤_ (λ _ → same) trans fork cmp
extrema : State → List (Point × Point)
extrema empty = []
extrema (active _ lo hi _) = (lo , hi) ∷ []
first-two : extrema (run (ε ▻ left ▻ low)) ≡ (low , left) ∷ []
first-two = refl
-- The incoming right is comparable with low but fails the test
-- against left. Thus the cached maximum detects the same forced cut.
answer : thinlist (ε ▻ left ▻ low ▻ right) ≡ ε ▻ low ▻ right
answer = refl
