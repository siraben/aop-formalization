{-# OPTIONS --safe --without-K #-}
module AoP.ParagraphWasteBalance where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; z≤; s≤)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _-_)
open import AoP.FractionCrossOrder using (module Arithmetic)
open Arithmetic using (assoc; swap; unit; sym)

-- Exercise 8.24. In a left-to-right layout the current (last) line
-- has no penalty. Closing a line of width w charges exactly margin-w.
-- Each break also replaces a one-column separator. Account for that
-- separator in both the flat text width and the per-break allowance.
module Balance (margin : Nat) where
  data Closed : Set where
    none : Closed
    break-at : ∀ w → w ≤ margin → Closed → Closed

  used charged allowance : Closed → Nat
  used none = 0
  used (break-at w _ ls) = suc w + used ls
  charged none = 0
  charged (break-at w _ ls) = (margin - w) + charged ls
  allowance none = 0
  allowance (break-at w _ ls) = suc margin + allowance ls

  private
    fill : ∀ w m → w ≤ m → (m - w) + w ≡ m
    fill 0 m p = unit m
    fill (suc w) (suc m) (s≤ p) = Arithmetic.move (m - w) w ∙ cong suc (fill w m p)
    exchange : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
    exchange a b c d = assoc a b (c + d) ∙ cong (a +_) (swap b c d) ∙ sym (assoc a c (b + d))

  account : ∀ ls → charged ls + used ls ≡ allowance ls
  account none = refl
  account (break-at w fits ls) = exchange (margin - w) (charged ls) (suc w) (used ls) ∙
    cong (_+ (charged ls + used ls)) (Arithmetic.move (margin - w) w ∙ cong suc (fill w margin fits)) ∙
    cong (suc margin +_) (account ls)

  -- Add the open line to both sides; its width contributes to the
  -- objective comparison, while its unused space is never charged.
  balance : ∀ ls last → charged ls + (used ls + last) ≡ allowance ls + last
  balance ls last = sym (assoc (charged ls) (used ls) last) ∙ cong (_+ last) (account ls)

module Example = Balance 6
open Example
-- Widths [2,2,1] fit as [2,2]|[1] or [2]|[2,1]. Both have one
-- break and flat width 7. The shorter last line gives less waste.
worked : (charged (break-at 5 (s≤ (s≤ (s≤ (s≤ (s≤ z≤))))) none) ≡ 1) ×
         (charged (break-at 2 (s≤ (s≤ z≤)) none) ≡ 4)
worked = refl , refl
