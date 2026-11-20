{-# OPTIONS --safe --without-K #-}
module AoP.BracketFrontierMinimum where

open import AoP.Prelude
open import AoP.Bracketing using (module Model)
open import AoP.BracketEnumeration using (complete)
open import AoP.BracketMinimum using (module Solve)
open import AoP.BracketSpineDominance using (module Law)
open import AoP.BracketFrontier using (module Build)
open import AoP.BracketFrontierCoverage using (module Cover)
open import AoP.ParagraphMinimum using (Dec)
open import AoP.NatOrder using (chain)
open import Agda.Builtin.Nat using (Nat)

-- The exhaustive and thinned searches return the same specification.
-- Scan only survivors. For an arbitrary competing tree, compare first
-- to its survivor and then use the spine bound to reach the competitor.
module Optimize {A S : Set} (atom : A → S) (combine : S → S → S) (charge : S → S → Nat)
                (eq? : ∀ (x y : S) → Dec (x ≡ y)) where
  open Model atom combine charge using (cost)
  open Solve cost using (Best; best; witness) renaming (module S to Scanner)
  open Build atom combine charge eq?
  open Cover atom combine charge eq? using (cover)
  open Law atom combine charge using (close)
  minimum : ∀ a xs → Best (a ∷ xs)
  minimum a xs with Scanner.scan (pool a xs)
  ... | Scanner.best t kept _ least = best t (valid a xs kept) λ u eq →
    let w , mem , p = cover a xs (complete _ u eq) in chain (least w mem tt) (snd (close p))
  ... | Scanner.none no with witness a xs
  ...   | u , eq with cover a xs (complete _ u eq)
  ...     | w , mem , p with no w mem tt
  ...       | ()
