{-# OPTIONS --safe --without-K #-}
module AoP.CachedVan where

open import AoP.Prelude
open import AoP.Reserves
open import AoP.VanSchedule
open import AoP.VanFold
open import AoP.ReserveExtrema
open import AoP.VaultCapacity
open import AoP.LineBreaks using (module Breaks)
open import AoP.Paragraph using (_∷⁺_)
open import AoP.ParagraphMinimum using (le?)
open import AoP.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat; _+_)

-- §7.5. Only the first block can be extended by the right fold. Cache
-- its two extrema; updating them takes one extend and one capacity test
-- per gap. Closed blocks need no further summaries.
module Cached (cap : Nat) where
  open Schedule cap using (Plan; Valid)
  open Fold cap using (Serviceable; nil; cons)
  open Breaks (λ (_ : Tx) → 0) 0
  head-needs : Plan → Needs
  head-needs ((u ∷⁺ us) ∷⁺ _) = summary (u ∷ us)

  record Result (t : Tx) (ts : List Tx) : Set where
    constructor result
    field
      plan : Plan
      partition : Partition t ts plan
      valid : Valid plan
      cache : Needs
      accurate : cache ≡ head-needs plan

  cost : Needs → Nat
  cost (need l h) = l + h

  solve : ∀ t ts → Serviceable (t ∷ ts) → Result t ts
  solve t [] (cons sec nil) = result _ (single t) sec _ refl
  solve t (v ∷ vs) (cons sec rest) with solve v vs rest
  ... | result ((u ∷⁺ us) ∷⁺ bs) part ok q eq with le? (cost (extend t q)) cap
  ...   | inr no = result _ (break-before-tail t part) (sec , ok) _ refl
  ...   | inl fits with bs | part | ok
  ...     | [] | p | _ = result _ (continue-line t p) (secure fits) (extend t q) (cong (extend t) eq)
    where
    secure : _ → Bank.Secure cap (t ∷ u ∷ us)
    secure le rewrite eq = Vault.enough cap _ le
  ...     | b ∷ tail | p | _ , others = result _ (continue-line t p) (secure fits , others) (extend t q) (cong (extend t) eq)
    where
    secure : _ → Bank.Secure cap (t ∷ u ∷ us)
    secure le rewrite eq = Vault.enough cap _ le
