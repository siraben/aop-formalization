{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.UpsequenceFrontier where

open import AoP.Common.Prelude
open import AoP.Chapter08.Bump using (module Prune)
open import AoP.Chapter08.UpsequenceDecision using (dominates?)
open import AoP.Chapter08.UpsequenceDominance using (module Law)
open import AoP.Common.NatOrder using (_≤_)
open import AoP.Chapter08.ParagraphMinimum using (le?)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Chapter01.Naturality using (_++_)
open import Agda.Builtin.Nat using (Nat)
open Law _≤_
module P = Prune Dominates reflexive (λ {x} {y} {z} → transitive x y z)

compare : ∀ x y → P.Comparison x y
compare x y with dominates? x y
... | inl p = P.first p
... | inr _ with dominates? y x
...   | inl p = P.second p
...   | inr _ = P.retain
module Pruning = P.Algorithm compare

-- Scan from right to left. Skip is always possible; take is possible
-- only when the new value precedes the old head. Thin after each step.
extensions : Nat → List (List Nat) → List (List Nat)
extensions a [] = []
extensions a ([] ∷ ys) = (a ∷ []) ∷ extensions a ys
extensions a ((b ∷ bs) ∷ ys) with le? a b
... | inl _ = (a ∷ b ∷ bs) ∷ extensions a ys
... | inr _ = extensions a ys

frontier : List Nat → List (List Nat)
frontier [] = [] ∷ []
frontier (a ∷ as) with frontier as
... | ys = Pruning.thinlist (extensions a ys ++ ys)

prune-step : ∀ a ys → Pruning.Covers (Pruning.thinlist (extensions a ys ++ ys)) (extensions a ys ++ ys)
prune-step a ys = Pruning.correct (extensions a ys ++ ys)
