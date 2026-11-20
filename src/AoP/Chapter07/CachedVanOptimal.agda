{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.CachedVanOptimal where

open import AoP.Common.Prelude
open import AoP.Chapter07.CachedVan using (module Cached)
open import AoP.Chapter07.CachedVanDecisions using (module Law)
open import AoP.Chapter07.VanSchedule using (module Schedule)
open import AoP.Chapter07.VanFold using (module Fold)
open import AoP.Chapter07.VanGreedyDominance using (module Proof)
open import AoP.Chapter07.VanGreedyStep using (module Law′)
open import AoP.Chapter07.VanHeadOrder using () renaming (module Law to Head)
open import AoP.Chapter07.SecurePartitionFold using () renaming (module Law to Guard)
open import AoP.Chapter08.Paragraph using (_∷⁺_)
open import AoP.Chapter08.LineBreaks using (module Breaks)
open import AoP.Chapter07.Reserves using (Tx)
open import AoP.Chapter01.ConversionCost using (len)
open import AoP.Common.NatOrder using (_≤_; s≤)
open import Agda.Builtin.Nat using (Nat; suc)

module Certificate (cap : Nat) where
  open Schedule cap hiding (solve)
  open Breaks (λ (_ : Tx) → 0) 0 using (Partition)
  open Cached cap
  open Fold cap using (Serviceable)
  blocks : ∀ p → Head.count Tx p ≡ suc (visits p)
  blocks (b ∷⁺ bs) = cong suc (size bs)
    where size : ∀ xs → len xs ≡ visits (b ∷⁺ xs)
          size [] = refl
          size (_ ∷ xs) = cong suc (size xs)

  fewer : ∀ p q → Head.count Tx p ≤ Head.count Tx q → visits p ≤ visits q
  fewer p q le rewrite blocks p | blocks q with le
  ... | s≤ n = n

  optimality : ∀ t ts (s : Serviceable (t ∷ ts)) q → Partition t ts q → Valid q → visits (Result.plan (solve t ts s)) ≤ visits q
  optimality t ts s q part ok = fewer (Result.plan (solve t ts s)) q (Law′.weak cap (Proof.dominates cap (Law.follows cap t ts s) (Guard.complete cap part ok)))

  certified : ∀ t ts → Serviceable (t ∷ ts) → Answer t ts
  certified t ts s = let r = solve t ts s in optimal (Result.plan r) (Result.partition r) (Result.valid r) (optimality t ts s)
