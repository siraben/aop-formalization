{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.LeftMinimumDirection where

open import AoP.Common.Prelude
open import AoP.Chapter08.LeftMinimumBlock using (module Block)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import AoP.Chapter08.Paragraph using (Nonempty; _∷⁺_)

-- Exercise 8.15. A right fold which never revisits a boundary can
-- miss the optimum. Its tail [2,1] must split. Prepending 0 to the
-- first block leaves [0,2]|[1], although [0,2,1] is itself valid.
-- The left-to-right strategy instead tests every new item against
-- the first element of the current block, not the previous item.
module Greedy {A : Set} (ok : (a b : A) → Bool) where
  Blocks = Nonempty (Nonempty A)
  right : A → List A → Blocks
  right a [] = (a ∷⁺ []) ∷⁺ []
  right a (b ∷ xs) with right b xs
  ... | (h ∷⁺ tail) ∷⁺ rest with ok a h
  ...   | true = (a ∷⁺ (h ∷ tail)) ∷⁺ rest
  ...   | false = (a ∷⁺ []) ∷⁺ ((h ∷⁺ tail) ∷ rest)

le : Nat → Nat → Bool
le 0 _ = true
le (Agda.Builtin.Nat.suc _) 0 = false
le (Agda.Builtin.Nat.suc a) (Agda.Builtin.Nat.suc b) = le a b

split-result : Greedy.right le 0 (2 ∷ 1 ∷ []) ≡ (0 ∷⁺ (2 ∷ [])) ∷⁺ ((1 ∷⁺ []) ∷ [])
split-result = refl
one-block : Block.LeftMin _≤_ 0 (2 ∷ 1 ∷ [])
one-block _ _ = z≤
