{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.MinimalSymmetry where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter07.MinimalComparison using (Test)
open import AoP.Chapter08.Thinning using (Min)

-- Exercise 7.23. A symmetric relation has no strict predecessor,
-- so every member is minimal. Conversely take the full set: if a
-- belongs to its minimal elements, each incoming edge at a reverses.
module Law {A : Set} (R : A ← A) where
  membership : ∀ {a X} → Min (Test R) a X → X a
  membership = fst

  all-minimal : R ˘ ⊆ R → ∀ {a} (X : A → Set) → X a → Min (Test R) a X
  all-minimal symmetric X member = member , λ b xb edge → symmetric edge

  symmetric : (∀ a (X : A → Set) → X a → Min (Test R) a X) → R ˘ ⊆ R
  symmetric every {a} {b} edge = snd (every a (λ _ → ⊤) tt) b tt edge
