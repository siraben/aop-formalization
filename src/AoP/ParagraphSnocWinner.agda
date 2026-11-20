{-# OPTIONS --safe --without-K #-}
module AoP.ParagraphSnocWinner where

open import AoP.Prelude
open import AoP.Snoc using (Snoc; ε; _▻_)
open import AoP.ParagraphSnocStep using (module Step)
open import AoP.ParagraphSnocFold using (module Layout)
open import AoP.ParagraphSnocWaste using (module Objective)
open import AoP.ParagraphAllowanceOrder using (module Law)
open import AoP.NatOrder using (_≤_)
open import Agda.Builtin.Nat using (Nat)

-- Supply one proof per word that it fits on an empty line. Build the
-- greedy history once, independently of any competing paragraph. The
-- winner may then be compared with arbitrarily many break patterns.
module Solve (m a : Nat) (fit : a ≤ m) where
  open Layout m a fit
  open Step m using (legal)
  open Objective m a fit using (waste; balance; fits; flat)
  open Law m using (waste-order)
  data Words : Snoc Nat → Set where
    empty : Words ε
    snoc : ∀ {ws w} → Words ws → w ≤ m → Words (ws ▻ w)
  winner : ∀ {ws} → Words ws → History ws (layout ws)
  winner empty = start
  winner (snoc ws p) = append (winner ws) (legal _ _ p)
  optimal : ∀ {ws s} (ok : Words ws) (h : History ws s) → waste (winner ok) ≤ waste h
  optimal {ws} ok h = waste-order (flat ws) _ _ _ _ (balance (winner ok)) (balance h) (fits (winner ok)) (snd (certified h))
