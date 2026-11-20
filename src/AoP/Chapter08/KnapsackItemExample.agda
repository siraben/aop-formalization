{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.KnapsackItemExample where

open import AoP.Common.Prelude
open import AoP.Chapter08.Knapsack using (module Packing)
open import AoP.Chapter08.KnapsackPackBridge using (module Law)
open import Agda.Builtin.Nat using (Nat)

-- Two distinct items have the same weight and value. At capacity four
-- the best single item (worth five) loses to taking both smaller ones.
data Item : Set where heavy red blue : Item
weight value : Item → Nat
weight heavy = 3
weight red = 2
weight blue = 2
value heavy = 5
value red = 3
value blue = 3
open Packing weight value using (Pack; empty; skip; take; worth)
open Law weight value using (solve-pack)
items = heavy ∷ red ∷ blue ∷ []
selected : ∀ {c xs} → Pack c xs → List Item
selected empty = []
selected (skip q) = selected q
selected (take {x = x} _ q) = x ∷ selected q

names : selected (fst (solve-pack 4 items)) ≡ red ∷ blue ∷ []
names = refl
score : worth (fst (solve-pack 4 items)) ≡ 6
score = refl
