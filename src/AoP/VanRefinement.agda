{-# OPTIONS --safe --without-K #-}
module AoP.VanRefinement where

open import AoP.Prelude
open import AoP.Reserves
open import AoP.VanTrimming
open import AoP.VanService
open import AoP.VanMinimum
open import AoP.VanSchedule
open import AoP.VanComparison
open import AoP.Naturality using (_++_)
open import AoP.Paragraph using (_∷⁺_)
open import AoP.LineBreaks using (module Breaks)
open import AoP.NatOrder using (_≤_; z≤; s≤; chain)
open import AoP.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat; suc)

-- Return the greedy solution through the exhaustive solver's public
-- Answer type. Thus either solver can serve the same specification, down
-- to its convention of counting internal visits on nonempty streams.
module Refine (cap : Nat) where
  open Trim cap hiding (cancel)
  open Schedule cap
  open Minimum cap
  open Breaks (λ (_ : Tx) → 0) 0
  open Compare cap using (compare-visits; translate)

  last-block : ∀ t ts → Partition t (ts ++ []) ((t ∷⁺ ts) ∷⁺ [])
  last-block t [] = single t
  last-block t (v ∷ vs) = continue-line t (last-block v vs)

  open AoP.Paragraph.Nonempty using (first; rest)
  prepend-block : ∀ t ts {v vs p} → Partition v vs p →
                  Partition t (ts ++ (v ∷ vs)) ((t ∷⁺ ts) ∷⁺ (first p ∷ rest p))
  prepend-block t [] {p = _ ∷⁺ _} part = break-before-tail t part
  prepend-block t (a ∷ as) part = continue-line t (prepend-block a as part)

  record Witness (n : Nat) (t : Tx) (ts : List Tx) : Set where
    constructor witness
    field
      plan : Plan
      part : Partition t ts plan
      valid : Valid plan
      fits : suc (visits plan) ≤ n

  recover : ∀ {n t ts} → Within n (t ∷ ts) → Witness n t ts
  recover (block {t = t} {ts = ts} {rest = []} sec _) = witness _ (last-block t ts) sec (s≤ z≤)
  recover (block {t = t} {ts = ts} {rest = v ∷ vs} sec tail) with recover tail
  ... | witness (b ∷⁺ bs) part ok fits = witness _ (prepend-block t ts part) (sec , ok) (s≤ fits)

  cancel : ∀ {a b} → suc a ≤ suc b → a ≤ b
  cancel (s≤ p) = p

  greedy : ∀ t ts → Answer t ts
  greedy t ts with Service.schedule cap (t ∷ ts)
  ... | inr no = impossible λ p part ok → no (translate p part ok)
  ... | inl g with recover (Opt.schedule g)
  ...   | witness p part ok fits = optimal p part ok λ q qp valid →
          cancel (chain fits (compare-visits g q qp valid))
