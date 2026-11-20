{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.ParagraphSquareFailure where

open import AoP.Common.Prelude
open import AoP.Chapter01.Snoc using (Snoc; ε; _▻_)
open import AoP.Chapter08.ParagraphSnocStep using (module Step)
open import AoP.Chapter08.ParagraphSnocFold using (module Layout)
open import AoP.Chapter08.ParagraphSnocWinner using (module Solve)
open import AoP.Chapter08.ParagraphSnocWaste using (module Objective)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; rid; weaken)
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat; _-_; _*_; _+_)

-- §8.5. The greedy theorem for additive waste cannot be reused when
-- each closed line's unused width is squared before summing.
private
  three : 3 ≤ 6
  three = s≤ (s≤ (s≤ z≤))
  two : 2 ≤ 6
  two = s≤ (s≤ z≤)
  five : 5 ≤ 6
  five = weaken (rid 5)
open Layout 6 3 three
open Solve 6 3 three
open Step 6 using (glue; line)
open Objective 6 3 three using (waste)

squared : ∀ {ws s} → History ws s → Nat
squared start = 0
squared (append h (glue _)) = squared h
squared (append {s = k , l} h (line _)) = (6 - l) * (6 - l) + squared h

-- Widths [3,2,2,5]. Greedy closes widths 6 and 2; moving the first
-- break one word earlier closes widths 3 and 5. Last width 5 is free.
words = ((ε ▻ 2) ▻ 2) ▻ 5
greedy = winner (snoc (snoc (snoc empty two) two) five)
rival : History words (2 , 5)
rival = append (append (append start (line two)) (glue five)) (line five)
linear-costs : (waste greedy ≡ 4) × (waste rival ≡ 4)
linear-costs = refl , refl
square-costs : (squared greedy ≡ 16) × (squared rival ≡ 10)
square-costs = refl , refl
fails : (∀ {s} (h : History words s) → squared greedy ≤ squared h) → ⊥
fails best = impossible (best rival)
  where impossible : 16 ≤ 10 → ⊥
        impossible (s≤ (s≤ (s≤ (s≤ (s≤ (s≤ (s≤ (s≤ (s≤ (s≤ ()))))))))))
