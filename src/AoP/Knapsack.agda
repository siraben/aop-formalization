{-# OPTIONS --safe --without-K #-}
module AoP.Knapsack where

open import AoP.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_)
open import AoP.PartyExample using (_≤_; z≤; s≤; rid; chain; sum-mono; compare)
open import AoP.Polynomial using (inl; inr)
open import AoP.Complement using (⊥)

absurd : ∀ {A : Set} → ⊥ → A
absurd ()

-- §8.4 — Pack each item at most once. With capacity 4, an item of
-- weight 3 and value 5 loses to two items of weight 2 and value 3 each.
-- The highest individual value therefore need not give the best packing.
-- This module gives a reference solver for checking a thinning algorithm:
-- try skipping the first item, and also taking it if it fits. The latter
-- branch gets only the remaining capacity. Nothing here claims that this
-- exhaustive solver has the running time of the book's pruned algorithm.
module Packing {Item : Set} (weight value : Item → Nat) where
  data Pack : Nat → List Item → Set where
    empty : ∀ {cap} → Pack cap []
    skip : ∀ {cap x xs} → Pack cap xs → Pack cap (x ∷ xs)
    take : ∀ {cap x xs} → weight x ≤ cap → Pack (cap - weight x) xs → Pack cap (x ∷ xs)

  worth : ∀ {cap xs} → Pack cap xs → Nat
  worth empty = 0
  worth (skip p) = worth p
  worth (take {x = x} fits p) = value x + worth p

  Best : Nat → List Item → Set
  Best cap xs = Σ (Pack cap xs) λ p → (q : Pack cap xs) → worth q ≤ worth p

  data Fit (w c : Nat) : Set where
    yes : w ≤ c → Fit w c
    no : (w ≤ c → ⊥) → Fit w c

  fits? : ∀ w c → Fit w c
  fits? zero c = yes z≤
  fits? (suc w) zero = no (λ ())
  fits? (suc w) (suc c) with fits? w c
  ... | yes p = yes (s≤ p)
  ... | no reject = no (λ { (s≤ p) → reject p })

  solve : ∀ cap xs → Best cap xs
  solve cap [] = empty , λ { empty → z≤ }
  solve cap (x ∷ xs) with solve cap xs | fits? (weight x) cap
  ... | p , best | no reject = skip p , λ where
    (skip q) → best q
    (take f q) → absurd (reject f)
  ... | p , best | yes f with solve (cap - weight x) xs
  ...   | r , opt with compare (worth p) (value x + worth r)
  ...     | inl wins = take f r , λ where
    (skip q) → chain (best q) wins
    (take _ q) → sum-mono (rid _) (opt q)
  ...     | inr loses = skip p , λ where
    (skip q) → best q
    (take _ q) → chain (sum-mono (rid _) (opt q)) loses
