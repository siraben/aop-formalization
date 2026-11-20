{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.InjectionAdjunction where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _∘_; _⊆_; _˘)
open import AoP.Chapter04.Shunting using (Id)
open import AoP.Chapter05.InjectionTests using (module Cases)
open import AoP.Chapter02.Polynomial using (inl; inr)

-- Proposition 4.1 in Rel. The unit supplies a round trip at input a.
-- For either direction of the claimed equality, the counit forces the
-- supplied intermediate output to equal the output of the given edge.
module Adj {A B : Set} (f : B ← A) (s : A ← B)
           (unit : Id ⊆ s ∘ f) (counit : f ∘ s ⊆ Id) where
  forward : s ⊆ f ˘
  forward {b = a} edge with unit {a = a} refl
  ... | b , u , v with counit (a , v , edge)
  ...   | refl = v
  backward : f ˘ ⊆ s
  backward {b = a} edge with unit {a = a} refl
  ... | b , u , v with counit (a , edge , u)
  ...   | refl = u

-- Exercise 5.12. Each reinjection is below the union of reinjections,
-- which equals identity; this gives the two counits. The units are the
-- successful matching-tag equations. Neither inference examines a tag.
module Read (A B : Set) where
  open Cases A B
  module Left = Adj L X left-ok′ (λ p → partition (inl p))
  module Right = Adj R Y right-ok′ (λ p → partition (inr p))
