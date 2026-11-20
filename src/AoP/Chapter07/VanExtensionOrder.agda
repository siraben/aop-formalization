{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.VanExtensionOrder where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_)
open import AoP.Chapter07.Reserves
open import AoP.Chapter07.VanHeadOrder using (module Law)
open import AoP.Chapter08.Paragraph using (_∷⁺_; module Layout)
open import Agda.Builtin.Nat using (Nat)

-- (7.21). When the smaller head is a prefix of the larger one, a
-- successful extension of the larger one certifies that the smaller
-- one can also be extended: stop its run at the prefix boundary.
module Proof (capacity : Nat) where
  open Bank capacity
  open Law Tx
  open Layout (λ (_ : Tx) → 0) 0 using (Para; glue)
  start : ∀ {ts a b} → Run ts a b → a ≤ capacity
  start (stop le) = le
  start (post le _ _) = le
  truncate : ∀ {xs ys a b} → Prefix xs ys → Run ys a b → Σ Nat (Run xs a)
  truncate empty run = _ , stop (start run)
  truncate (keep _ p) (post le tx run) with truncate p run
  ... | _ , earlier = _ , post le tx earlier

  extend : ∀ a p q → count p ≤ count q → H p q → Secure (a ∷ first-block q) →
           Secure (a ∷ first-block p) × ((count (glue a p) ≤ count (glue a q)) × H (glue a p) (glue a q))
  extend a ((u ∷⁺ us) ∷⁺ ls) ((v ∷⁺ vs) ∷⁺ ms) le h (r , s , run) with truncate (keep a h) run
  ... | end , short = (r , end , short) , le , keep a h
