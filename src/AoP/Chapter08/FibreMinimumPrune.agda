{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.FibreMinimumPrune where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter08.Thinning

-- Exercise 8.11, the local pruning step for layered networks. A
-- transition chooses an intermediate state i and then an output from
-- its fibre. Keep all cost minima within each enabled fibre. Though
-- cost alone need not simulate a future transition, cost comparison
-- inside a common fibre is assumed to imply the simulation order Q.
module Prune {I B : Set} (S : B ← I) (enabled : Pred I) (R Q : B ← B)
             (safe : R ⊓ (S ∘ S ˘) ⊆ Q) where
  Reach Kept : Pred B
  Reach b = Σ I λ i → enabled i × S b i
  Kept b = Σ I λ i → enabled i × Min R b (λ c → S c i)

  feasible : ∀ {b} → Kept b → Reach b
  feasible (i , on , member , _) = i , on , member

  sound-pruning : (∀ i → enabled i → ∀ b → S b i → Σ B λ a → Min R a (λ c → S c i)) → Thin Q Kept Reach
  sound-pruning choose = thin feasible cover
    where cover : ∀ b → Reach b → Σ B λ a → Kept a × Q a b
          cover b (i , on , sb) with choose i on b sb
          ... | a , sa , lower = a , (i , on , sa , lower) , safe (lower b sb , i , sa , sb)
