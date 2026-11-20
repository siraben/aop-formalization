{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.OneWayMonotone where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Complement using (⊥)

-- §7.2, identity shape. The low input returns high; the high input
-- can return either value. Increasing the input always permits a
-- matching output at least as high. Decreasing the input from high
-- to low cannot match the extra low output of the high input.
data Level : Set where low high : Level
data Le : Level ← Level where
  same : ∀ {x} → Le x x
  increase : Le low high

data Choice : Level ← Level where
  top : ∀ {x} → Choice high x
  extra : Choice low high

monotone : Choice ∘ Le ⊆ Le ∘ Choice
monotone (x , choice , same) = _ , same , choice
monotone (_ , top , increase) = high , same , top

fails-converse : (Choice ∘ (Le ˘) ⊆ (Le ˘) ∘ Choice) → ⊥
fails-converse sub with sub (_ , extra , increase)
... | _ , () , top
