{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.VanLexMinimumExample where

open import AoP.Common.Prelude
open import AoP.Chapter07.Reserves
open import AoP.Chapter08.Paragraph using (_∷⁺_; Nonempty)
open import AoP.Chapter08.LineBreaks using (module Breaks)
open import AoP.Chapter07.VanSchedule using (module Schedule)
open import AoP.Chapter07.VanLexOrder using (module Order)
open import AoP.Chapter07.VanHeadOrder using (module Law)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; rid)
open import AoP.Chapter04.Complement using (⊥)

-- With the prefix orientation printed in 7.57, a Q-minimum can
-- prefer splitting even when the whole stream fits. These are all
-- partitions of two deposits of one at capacity two.
open Bank 2
open Schedule 2 using (Plan; visits; Valid)
open Breaks (λ (_ : Tx) → 0) 0 using (Partition; single; break-before-tail; continue-line)
open Order Tx
open Law Tx using (keep; empty)
a = deposit 1
single-block = a ∷⁺ []
split-plan = single-block ∷⁺ (single-block ∷ [])
joined = (a ∷⁺ (a ∷ [])) ∷⁺ []
parts : Plan → Blocks
parts ((x ∷⁺ xs) ∷⁺ bs) = (x ∷ xs) ∷ rest bs
  where rest : List (Nonempty Tx) → Blocks
        rest [] = []
        rest ((u ∷⁺ us) ∷ vs) = (u ∷ us) ∷ rest vs
short : Secure (a ∷ [])
short = 0 , 1 , post z≤ (credit 1 0) (stop (s≤ z≤))
valid-split : Valid split-plan
valid-split = short , short
valid-joined : Valid joined
valid-joined = 0 , 2 , post z≤ (credit 1 0) (post (s≤ z≤) (credit 1 1) (stop (rid 2)))
partition-split : Partition a (a ∷ []) split-plan
partition-split = break-before-tail a (single a)
partition-joined : Partition a (a ∷ []) joined
partition-joined = continue-line a (single a)
minimum-Q : ∀ {p} → Partition a (a ∷ []) p → Q (parts split-plan) (parts p)
minimum-Q (break-before-tail _ (single _)) = reflQ _
minimum-Q (continue-line _ (single _)) = keep a empty , λ { (keep _ ()) }
not-minimum-count : visits split-plan ≤ visits joined → ⊥
not-minimum-count ()
