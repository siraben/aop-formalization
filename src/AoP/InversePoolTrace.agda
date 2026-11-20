{-# OPTIONS --safe --without-K #-}
module AoP.InversePoolTrace where

open import AoP.Prelude
open import AoP.Snoc using (ε; _▻_)
open import AoP.DictionaryTableTrace using (Letter; a; eq?)
open import AoP.DictionaryStateExpand using (module Fold)
open import AoP.DictionaryStateMinimum using (module Solver)
open import AoP.DictionaryThinState using (module State)
open import AoP.DictionarySplice using (module Splice)
open import AoP.DictionaryStatePrune using (module Pool)
open import AoP.Compression using (module Text)
open import Agda.Builtin.Nat using (Nat)

-- Trace the actual inverse-fold pool. It can retain several entries
-- with the same key: the sweep guarantees coverage, not uniqueness.
open Fold eq? 2 3 using (table)
open Pool eq? 2 3 using (Candidate)
open State {Letter} 2 3 using (program)
open Splice {Letter} 2 3 using (price)
open Text {Letter}
costs : ∀ {ys} → List (Candidate ys) → List Nat
costs [] = []
costs (w ∷ ws) = price (program (snd w)) ∷ costs ws
one = ε ▻ a
two = one ▻ a
three = two ▻ a
at-two : costs (table two) ≡ 4 ∷ 5 ∷ []
at-two = refl
at-three : costs (table three) ≡ 6 ∷ 7 ∷ 7 ∷ 7 ∷ 8 ∷ 8 ∷ 5 ∷ []
at-three = refl
winner : fst (Solver.solve eq? 2 3 three) ≡ sym a ∷ ptr 0 1 ∷ []
winner = refl
