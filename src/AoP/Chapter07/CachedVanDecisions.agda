{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.CachedVanDecisions where

open import AoP.Common.Prelude
open import AoP.Chapter07.CachedVan using (module Cached)
open import AoP.Chapter07.VanFold using (module Fold)
open import AoP.Chapter07.VanGreedyDominance using (module Proof)
open import AoP.Chapter07.VaultCapacity using (module Vault)
open import AoP.Chapter07.ReserveExtrema using (extend)
open import AoP.Chapter08.Paragraph using (_∷⁺_)
open import AoP.Chapter08.ParagraphMinimum using (le?)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat)

-- Link the implementation to the greedy derivation: rewriting by the
-- cache invariant turns each test into the necessary and sufficient
-- capacity bound for the block with its new first transaction.
module Law (cap : Nat) where
  open Fold cap using (Serviceable; cons; nil)
  open Cached cap
  open Proof cap
  follows : ∀ t ts (s : Serviceable (t ∷ ts)) → Greedy t ts (Result.plan (solve t ts s))
  follows t [] (cons ok nil) = start t
  follows t (v ∷ vs) (cons ok rest) with solve v vs rest | follows v vs rest
  ... | result ((u ∷⁺ us) ∷⁺ bs) part valid ._ refl | g with le? (cost (extend t (head-needs ((u ∷⁺ us) ∷⁺ bs)))) cap
  ...   | inr no = split t (λ sec → no (Vault.required cap _ sec)) g
  ...   | inl yes with bs | part | valid | g
  ...     | [] | q | good | h = join′ t (Vault.enough cap _ yes) h
  ...     | b ∷ tail | q | good , others | h = join′ t (Vault.enough cap _ yes) h
