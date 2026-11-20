{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.ParagraphSnocFold where

open import AoP.Common.Prelude
open import AoP.Chapter01.Snoc using (Snoc; ε; _▻_; foldl)
open import AoP.Chapter08.ParagraphSnocStep using (State; _≼_; narrower; module Step)
open import AoP.Common.NatOrder using (_≤_; rid; z≤; s≤)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 8.24. Start with one word on the open line. A history
-- records, for each subsequent word, whether it was glued or began a
-- line. A rival history also certifies that each word fits by itself.
module Layout (margin first : Nat) (fits : first ≤ margin) where
  open Step margin
  data History : Snoc Nat → State → Set where
    start : History ε (0 , first)
    append : ∀ {ws s w t} → History ws s → Next w s t → History (ws ▻ w) t

  layout : Snoc Nat → State
  layout = foldl (0 , first) (λ s w → choose w s)
  private
    pad : ∀ w l → w ≤ width w l
    pad 0 l = z≤
    pad (Agda.Builtin.Nat.suc w) l = s≤ (pad w l)
    word-fits : ∀ {w s t} → Next w s t → w ≤ margin
    word-fits (line p) = p
    word-fits {w} (glue {l = l} p) = AoP.Common.NatOrder.chain (pad w l) p

  certified : ∀ {ws t} → History ws t → History ws (layout ws) × (layout ws ≼ t)
  certified start = start , narrower (rid _)
  certified (append h n) with certified h
  ... | greedy , advantage = append greedy (legal _ _ (word-fits n)) , dominates _ advantage n

module Example = Layout 6 2 (s≤ (s≤ z≤))
words = (ε ▻ 2) ▻ 1
result : Example.layout words ≡ (1 , 1)
result = refl
