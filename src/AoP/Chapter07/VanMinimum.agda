{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.VanMinimum where

open import AoP.Common.Prelude
open import AoP.Chapter07.Reserves
open import AoP.Chapter07.LongestPrefix
open import AoP.Chapter07.VanTrimming
open import AoP.Chapter07.VanBudget using (module Greedy)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- §7.5. Given any feasible budget, compute the minimum block count in
-- one greedy pass over successive suffixes. The incoming plan supplies
-- a termination bound; its choices never determine the van stops.
module Minimum (cap : Nat) where
  open Bank cap
  open Prefix {Tx}
  open Trim cap
  open Greedy cap using (cast; absurd-prefix)

  record Opt (xs : List Tx) : Set where
    constructor optimal
    field
      count : Nat
      schedule : Within count xs
      least : ∀ {m} → Within m xs → count ≤ m

  lift-lower : ∀ {t ts k} (g : Longest Secure (t ∷ ts)) →
               (∀ {m} → Within m (Longest.rest g) → k ≤ m) →
               ∀ {m} → Within m (t ∷ ts) → suc k ≤ m
  lift-lower g lower {suc m} p = s≤ (lower (exchange g p))

  solve : ∀ {xs} n → Within n xs → Opt xs
  solve {[]} n p = optimal 0 done (λ _ → z≤)
  solve {t ∷ ts} (suc n) p with Van.first-block cap (t ∷ ts)
  ... | result [] r eq ok dom with p
  ...   | block {t = a} {ts = as} {rest = rest} sec tail =
          absurd (absurd-prefix (dom (prefix (a ∷ as) rest) sec))
  solve {t ∷ ts} (suc n) p | g@(result (a ∷ as) r eq ok dom) with solve n (exchange g p)
  ... | optimal k tail least = optimal (suc k) (cast eq (block ok tail)) (lift-lower g least)
