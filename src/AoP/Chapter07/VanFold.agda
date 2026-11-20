{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.VanFold where

open import AoP.Common.Prelude
open import AoP.Chapter07.Reserves
open import AoP.Chapter07.SecureBlock
open import AoP.Chapter07.VanSchedule
open import AoP.Chapter08.LineBreaks using (module Breaks)
open import AoP.Chapter08.Paragraph using (_∷⁺_)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat)

-- §7.5's fold processes the stream from the right. Insert the next
-- transaction into the first block if it still fits; otherwise start a
-- fresh block. This direction matters for the actual visit locations.
-- For [+4,+4,+4] at capacity ten, the suffix [+4,+4] stays together.
-- Here `secure?` implements the test by reserve search. The constant-
-- summary implementation based on the prefix extrema is a further step.
module Fold (cap : Nat) where
  open Bank cap
  open Schedule cap
  open Breaks (λ (_ : Tx) → 0) 0

  -- Service requires each individual transaction to fit in the vault.
  data Serviceable : List Tx → Set where
    nil : Serviceable []
    cons : ∀ {t ts} → Secure (t ∷ []) → Serviceable ts → Serviceable (t ∷ ts)

  record Output (t : Tx) (ts : List Tx) : Set where
    constructor out
    field
      plan : Plan
      partition : Partition t ts plan
      valid : Valid plan

  schedule : ∀ t ts → Serviceable (t ∷ ts) → Output t ts
  schedule t [] (cons sec _) = out _ (single t) sec
  schedule t (v ∷ vs) (cons sec rest) with schedule v vs rest
  ... | out ((u ∷⁺ us) ∷⁺ bs) part ok with Check.secure? cap (t ∷ u ∷ us)
  ...   | inr _ = out _ (break-before-tail t part) (sec , ok)
  ...   | inl extended with bs | ok | part
  ...     | [] | _ | q = out _ (continue-line t q) extended
  ...     | b ∷ tail | _ , others | q = out _ (continue-line t q) (extended , others)
