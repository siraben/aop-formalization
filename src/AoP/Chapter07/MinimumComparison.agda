{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.MinimumComparison where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter08.Thinning using (Min)
open import AoP.Chapter07.TwoMinima using (module Law)

-- Exercise 7.9. Take the second relation of 7.8 to be universal:
-- being its minimum asks only that b belong to the witnessing set.
module Recover {A : Set} (R : A ← A) (rr : ∀ a → R a a) where
  module Pair = Law R (λ _ _ → ⊤)
  Witness : A → A → Set₁
  Witness a b = Σ (A → Set) λ X → Min R a X × X b

  recover : ∀ {a b} → Witness a b → R a b
  recover (X , (_ , lower) , member) = lower _ member

  represent : ∀ {a b} → R a b → Witness a b
  represent edge with Pair.witness rr (λ _ → tt) (edge , tt)
  ... | X , minimum , member , _ = X , minimum , member

-- Exercise 7.10. Inclusion of the underlying relations transports
-- minima on every set. Test the converse on the witness from 7.9.
module Compare {A : Set} (R S : A ← A) where
  Included = ∀ a (X : A → Set) → Min R a X → Min S a X

  forward : R ⊆ S → Included
  forward sub a X (member , lower) = member , λ b x → sub (lower b x)

  backward : (∀ a → R a a) → Included → R ⊆ S
  backward rr sub {a} {b} edge with Recover.represent R rr edge
  ... | X , minimum , member = snd (sub a X minimum) b member
