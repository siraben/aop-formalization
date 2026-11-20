{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXFirstGrid where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; z≤; s≤)
open import AoP.Chapter10.OpenUpperDigit using (Upper)
open import AoP.Chapter10.TeXGridStop using (InCell; module Grid)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

-- Search successive decimal grids, given their greatest numerators
-- below the open upper endpoint. A feasible last width supplies fuel.
record Answer (W : Nat) (L H : Nat → Nat) : Set where
  constructor answer
  field places value : Nat
        fits : InCell W (L places) (H places) value
        shortest : ∀ k t → InCell W (L k) (H k) t → places ≤ k
        greatest : ∀ t → InCell W (L places) (H places) t → t ≤ value
private
  decide : ∀ x y → (x ≤ y) ⊎ (suc y ≤ x)
  decide 0 y = inl z≤
  decide (suc x) 0 = inr (s≤ z≤)
  decide (suc x) (suc y) with decide x y
  ... | inl p = inl (s≤ p)
  ... | inr p = inr (s≤ p)
  absurd : ∀ {X : Set} → ⊥ → X
  absurd ()

scan : ∀ (limit W : Nat) (L H z : Nat → Nat) → (∀ k → Upper W (H k) (z k)) → InCell W (L limit) (H limit) (z limit) → Answer W L H
scan 0 W L H z u last = answer 0 (z 0) last (λ k t p → z≤) (λ t p → Grid.dominates W (L 0) (H 0) (z 0) (u 0) t (snd p))
scan (suc k) W L H z u last with decide (L 0) (z 0 * W)
... | inl ok = answer 0 (z 0) (ok , fst (u 0)) (λ i t p → z≤) (λ t p → Grid.dominates W (L 0) (H 0) (z 0) (u 0) t (snd p))
... | inr gap = answer (suc places) value fits minimal greatest
  where
  open Answer (scan k W (λ i → L (suc i)) (λ i → H (suc i)) (λ i → z (suc i)) (λ i → u (suc i)) last)
  minimal : ∀ i t → InCell W (L i) (H i) t → suc places ≤ i
  minimal 0 t p = absurd (Grid.skip W (L 0) (H 0) (z 0) (u 0) gap t p)
  minimal (suc i) t p = s≤ (shortest i t p)
