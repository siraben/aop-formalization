{-# OPTIONS --safe --without-K #-}
module AoP.CachedVanExample where

open import AoP.Prelude
open import AoP.Reserves
open import AoP.VaultCapacity
open import AoP.VanFold
open import AoP.CachedVan
open import AoP.Paragraph using (_∷⁺_)
open import AoP.VanSchedule using (module Schedule)
open import AoP.NatOrder using (rid)
open import AoP.VanComparison
open import AoP.VanService
open import AoP.VanMinimum
open import AoP.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat; suc)

-- Two optimal schedules for the same bank. The vault holds ten; it
-- cannot absorb three deposits of four without service. The left-to-right
-- solver groups the first two deposits (VanExample.latest-visit). The
-- book's right fold groups the last two. Check the actual blocks and
-- certify that the example meets the global lower bound on visit count.
open Fold 10 using (Serviceable; cons; nil)
open Cached 10 using (Result; solve)
open Schedule 10 using (Plan; visits; Valid)
open import AoP.LineBreaks using (module Breaks)
open Breaks (λ (_ : Tx) → 0) 0 using (Partition)
open import AoP.NatOrder using (_≤_; s≤; z≤)

d = deposit 4
unit : Bank.Secure 10 (d ∷ [])
unit = Vault.enough 10 _ (s≤ (s≤ (s≤ (s≤ z≤))))

serviceable : Serviceable (d ∷ d ∷ d ∷ [])
serviceable = cons unit (cons unit (cons unit nil))

solution = solve d (d ∷ d ∷ []) serviceable

first-gap : Result.plan solution ≡ (d ∷⁺ []) ∷⁺ ((d ∷⁺ (d ∷ [])) ∷ [])
first-gap = refl

-- Compute the independent left-greedy optimum and apply its lower bound
-- to *any* partition. No comparison between the two lists of stops is
-- needed, so the tie does not affect the certificate.
optimal-visits : ∀ p → Partition d (d ∷ d ∷ []) p → Valid p → visits (Result.plan solution) ≤ visits p
optimal-visits p part ok = strip (Compare.compare-visits 10 winner p part ok)
  where
  winner : Minimum.Opt 10 (d ∷ d ∷ d ∷ [])
  winner with Service.schedule 10 (d ∷ d ∷ d ∷ [])
  ... | inl g = g
  ... | inr no = Prefix.absurd {A = Tx} (no (Compare.translate 10 _ (Result.partition solution) (Result.valid solution)))
    where open import AoP.LongestPrefix
  strip : ∀ {a b} → suc a ≤ suc b → a ≤ b
  strip (s≤ le) = le
