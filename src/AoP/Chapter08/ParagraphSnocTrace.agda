{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.ParagraphSnocTrace where

open import AoP.Common.Prelude
open import AoP.Chapter08.ParagraphSnocStep using (module Step)
open import AoP.Chapter08.ParagraphSnocFold using (module Example; words)
open import AoP.Chapter08.ParagraphSnocWaste using (module Objective)
open import AoP.Common.NatOrder using (s≤; z≤; _≤_)
open import Agda.Builtin.Nat using (Nat)
open Example
open Step 6 using (glue; line)
open Objective 6 2 (s≤ (s≤ z≤)) using (minimum; waste)

-- Two rival histories for [2,2,1]. Both use one break, but ending
-- the first line after one word throws away four columns instead of
-- one. Recover the greedy history from the general theorem applied
-- to that strictly worse rival, then inspect its actual decisions.
rival : History words (1 , 4)
rival = append (append start (line (s≤ (s≤ z≤)))) (glue (s≤ (s≤ (s≤ (s≤ z≤)))))

data Action : Set where join split : Action
actions : ∀ {ws s} → History ws s → List Action
actions start = []
actions (append h (glue _)) = join ∷ actions h
actions (append h (line _)) = split ∷ actions h

winner = fst (minimum rival)
-- The outermost constructor is the last word, so these traces are
-- read right-to-left in the order the words were appended.
rival-trace : actions rival ≡ join ∷ split ∷ []
rival-trace = refl
winner-trace : actions winner ≡ split ∷ join ∷ []
winner-trace = refl
costs : (waste winner ≡ 1) × (waste rival ≡ 4)
costs = refl , refl
