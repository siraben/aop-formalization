{-# OPTIONS --safe --without-K #-}
module AoP.LayeredHeadCache where

open import AoP.Prelude
open import AoP.LayeredCostFold using (module Paths)
open import AoP.NatOrder using (_≤_)
open import Agda.Builtin.Nat using (Nat; _+_)

-- §8.2's implementation stores the triple (path, head, cost).
-- Prepending reads only the two cached fields of the old path.
module Cache {V : Set} (wt : V → V → Nat) where
  open Paths wt using (Path; single; via; head; cost; fold)
  Packed = Path × (V × Nat)
  pack : Path → Packed
  pack p = p , head p , cost p
  wrap : V → Packed
  wrap a = single a , a , 0
  push : V → Packed → Packed
  push a (p , b , n) = via a p , a , wt a b + n
  build = fold wrap push
  exact : ∀ p → build p ≡ pack p
  exact (single a) = refl
  exact (via a p) = cong (push a) (exact p)
  compare-extension : ∀ a p q → snd (snd (push a (build p))) ≤ snd (snd (push a (build q))) → cost (via a p) ≤ cost (via a q)
  compare-extension a p q rewrite exact p | exact q = λ le → le

module Trace where
  open import AoP.LayeredCostFold using (weight; root; east; e)
  open Paths weight using (via)
  open Cache weight
  suffix : build e ≡ (e , east , 5)
  suffix = refl
  complete : push root (build e) ≡ (via root e , root , 6)
  complete = refl
