{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.LayoutTie where

open import AoP.Common.Prelude
open import AoP.Chapter08.Paragraph using (_∷⁺_; module Layout)
open import AoP.Chapter08.LineBreaks using (module Breaks)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; rid; weaken)
open import Agda.Builtin.Nat using (Nat; suc)

-- Exercise 7.56. Three one-letter words at margin three need two
-- lines. Both break positions minimize line count, but the first
-- leaves two unused columns on the nonfinal line and the second none.
open Layout (λ (n : Nat) → n) 3
open Breaks (λ (n : Nat) → n) 3
short-first = new 1 (glue 1 ((1 ∷⁺ []) ∷⁺ []))
full-first = glue 1 (new 1 ((1 ∷⁺ []) ∷⁺ []))
Text = Partition 1 (1 ∷ 1 ∷ [])
short-text : Text short-first
short-text = break-before-tail 1 (continue-line 1 (single 1))
full-text : Text full-first
full-text = continue-line 1 (break-before-tail 1 (single 1))
short-fits : Fits short-first
short-fits = s≤ z≤ , rid 3
full-fits : Fits full-first
full-fits = rid 3 , s≤ z≤

open import AoP.Chapter01.ConversionCost using (len)
count : Para → Nat
count (_ ∷⁺ ls) = suc (len ls)

minimum : ∀ {p} → Text p → Fits p → 2 ≤ count p
minimum (break-before-tail _ (break-before-tail _ (single _))) _ = weaken (rid 2)
minimum (break-before-tail _ (continue-line _ (single _))) _ = rid 2
minimum (continue-line _ (break-before-tail _ (single _))) _ = rid 2
minimum (continue-line _ (continue-line _ (single _))) (s≤ (s≤ (s≤ ())))

tie : count short-first ≡ count full-first
tie = refl
short-waste : waste (λ n → n) short-first ≡ 2
short-waste = refl
full-waste : waste (λ n → n) full-first ≡ 0
full-waste = refl
