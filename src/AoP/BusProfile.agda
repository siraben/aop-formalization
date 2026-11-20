{-# OPTIONS --safe --without-K #-}
module AoP.BusProfile where

open import AoP.Prelude
open import AoP.BusWalking using (distance; module Layout)
open import AoP.Subsequences using (here; there; _∈_)
open import AoP.NatOrder using (_≤_; rid; chain)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 8.31. Compare two same-quota partial layouts on the blocks
-- carrying demand. If every block is at least as close in the first,
-- it remains so when we add the same stop to both layouts.
record Stops : Set where
  constructor sites
  field first : Nat
        rest : List Nat
open Stops
near : Stops → Nat → Nat
near (sites x xs) j = distance j (fst (Layout.nearest x xs j))
add : Nat → Stops → Stops
add k (sites x xs) = sites k (x ∷ xs)

insert-bound : ∀ k l r j → near l j ≤ near r j → near (add k l) j ≤ near (add k r) j
insert-bound k (sites x xs) (sites y ys) j le with Layout.nearest k (y ∷ ys) j
... | .k , here , best = snd (snd (Layout.nearest k (x ∷ xs) j)) k here
... | b , there m , best = chain via-old (chain le (snd (snd (Layout.nearest y ys j)) b m))
  where via-old : near (sites k (x ∷ xs)) j ≤ near (sites x xs) j
        via-old = snd (snd (Layout.nearest k (x ∷ xs) j)) _ (there (fst (snd (Layout.nearest x xs j))))

Profile : List Nat → Stops → Stops → Set
Profile blocks l r = ∀ j → j ∈ blocks → near l j ≤ near r j
extend : ∀ blocks k l r → Profile blocks l r → Profile blocks (add k l) (add k r)
extend blocks k l r p j m = insert-bound k l r j (p j m)
