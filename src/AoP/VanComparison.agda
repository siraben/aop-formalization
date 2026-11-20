{-# OPTIONS --safe --without-K #-}
module AoP.VanComparison where

open import AoP.Prelude
open import AoP.Reserves
open import AoP.VanMinimum
open import AoP.VanBudget
open import AoP.VanTrimming
open import AoP.VanSchedule
open import AoP.Paragraph using (module Layout; _∷⁺_)
open import AoP.LineBreaks using (module Breaks)
open import AoP.NatOrder using (_≤_)
open import Agda.Builtin.Nat using (Nat; suc)

-- Relate the two §7.5 specifications. A partition with v internal
-- visits has exactly v+1 nonempty blocks. Translate it into a budget
-- witness; then the greedy lower bound applies to the very same plans
-- that the exhaustive solver enumerates, including its winning plan.
module Compare (cap : Nat) where
  open Schedule cap
  open Trim cap
  open Minimum cap
  open Layout (λ (_ : Tx) → 0) 0 using (words)
  open Breaks (λ (_ : Tx) → 0) 0 using (Partition; preserves-text)

  budget : ∀ b bs → feasible b bs → Within (suc (visits (b ∷⁺ bs))) (words (b ∷⁺ bs))
  budget (t ∷⁺ ts) [] sec = block sec done
  budget (t ∷⁺ ts) (b ∷ bs) (sec , tail) = block sec (budget b bs tail)

  translate : ∀ {t ts} p → Partition t ts p → Valid p → Within (suc (visits p)) (t ∷ ts)
  translate (b ∷⁺ bs) part ok = Greedy.cast cap (preserves-text part) (budget b bs ok)

  compare-visits : ∀ {t ts} (g : Opt (t ∷ ts)) p → Partition t ts p → Valid p →
                   Opt.count g ≤ suc (visits p)
  compare-visits g p part ok = Opt.least g (translate p part ok)
