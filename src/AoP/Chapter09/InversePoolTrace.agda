{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.InversePoolTrace where

open import AoP.Common.Prelude
open import AoP.Chapter01.Snoc using (ε; _▻_)
open import AoP.Chapter09.DictionaryTableTrace using (Letter; a; eq?)
open import AoP.Chapter09.DictionaryStateExpand using (module Fold)
open import AoP.Chapter09.DictionaryStateMinimum using (module Solver)
open import AoP.Chapter09.DictionaryThinState using (module State)
open import AoP.Chapter09.DictionarySplice using (module Splice)
open import AoP.Chapter09.DictionaryStatePrune using (module Pool)
open import AoP.Chapter09.Compression using (module Text)
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
