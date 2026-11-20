{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.MinimalComparison where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Complement using (⊥)

-- Exercise 7.19. Minimality tests whether each incoming comparison
-- can be reversed. At the candidate itself this test is an identity.
Test : ∀ {A} → (A ← A) → A ← A
Test R a b = R b a → R a b

reflexive : ∀ {A} (R : A ← A) a → Test R a a
reflexive R a edge = edge

-- A preorder with a single strict edge low ≤ high and an isolated
-- point mid. The test passes from high to mid and from mid to low
-- because both are incomparable pairs. It fails from high to low.
data Point : Set where low mid high : Point
data Order : Point ← Point where
  same : ∀ {p} → Order p p
  strict : Order low high

transitive : Order ∘ Order ⊆ Order
transitive (_ , same , q) = q
transitive (_ , strict , same) = strict

high-mid : Test Order high mid
high-mid ()
mid-low : Test Order mid low
mid-low ()

fails : (Test Order ∘ Test Order ⊆ Test Order) → ⊥
fails tr with tr {high} {low} (mid , high-mid , mid-low) strict
... | ()
