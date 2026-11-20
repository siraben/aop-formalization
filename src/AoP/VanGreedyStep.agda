{-# OPTIONS --safe --without-K #-}
module AoP.VanGreedyStep where

open import AoP.Prelude
open import AoP.Reserves
open import AoP.VanHeadOrder using (module Law)
open import AoP.VanExtensionOrder using (module Proof)
open import AoP.Paragraph using (module Layout; _∷⁺_)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Complement using (⊥)
open import AoP.NatOrder using (_≤_; s≤; chain; rid; weaken)
open import Agda.Builtin.Nat using (Nat; suc)

-- Refined dominance: fewer blocks suffice; otherwise maintain both
-- the block comparison and a prefix witness on the first block.
module Law′ (cap : Nat) where
  open Bank cap
  open Law Tx
  open Proof cap using (extend)
  open Layout (λ (_ : Tx) → 0) 0 using (Para; new; glue)
  Better : Para → Para → Set
  Better p q = (suc (count p) ≤ count q) ⊎ ((count p ≤ count q) × H p q)
  weak : ∀ {p q} → Better p q → count p ≤ count q
  weak {p} (inl strict) = chain (weaken (rid (count p))) strict
  weak (inr (le , _)) = le

  -- When glue succeeds it dominates either legal choice for q.
  glue-new : ∀ a p q → Better p q → Better (glue a p) (new a q)
  glue-new a ((u ∷⁺ us) ∷⁺ ls) q d = inl (s≤ (weak d))
  glue-glue : ∀ a p q → Better p q → Better (glue a p) (glue a q)
  glue-glue a ((u ∷⁺ us) ∷⁺ ls) ((v ∷⁺ vs) ∷⁺ ms) (inl lt) = inl lt
  glue-glue a ((u ∷⁺ us) ∷⁺ ls) ((v ∷⁺ vs) ∷⁺ ms) (inr (le , h)) = inr (le , keep a h)

  -- With a failed glue, the competitor can glue only if p had a
  -- strict lead to spend. Otherwise truncating its run refutes failure.
  new-vs-new : ∀ a p q → Better p q → Better (new a p) (new a q)
  new-vs-new a p q d = inr (s≤ (weak d) , new-new a p q)
  new-vs-glue : ∀ a p q → Better p q → (Secure (a ∷ first-block p) → ⊥) → Secure (a ∷ first-block q) → Better (new a p) (glue a q)
  new-vs-glue a p q (inl lt) no ok = inr (new-count a p q lt , new-old a p q)
  new-vs-glue a p q (inr (le , h)) no ok with no (fst (extend a p q le h ok))
  ... | ()
