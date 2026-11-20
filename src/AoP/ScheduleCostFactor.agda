{-# OPTIONS --safe --without-K #-}
module AoP.ScheduleCostFactor where

open import AoP.Prelude
open import AoP.Snoc using (Snoc; ε; _▻_)
open import AoP.Tardiness using (Job; cost; elapsed; penalty)
open import AoP.Trees using (max)
open import Agda.Builtin.Nat using (Nat; suc)

-- Exercise 10.6. Split the final constructor into the newly incurred
-- penalty and the cost already incurred. Both components are zero on
-- the empty branch. The objective combines them by maximum.
data Layer : Set where
  empty : Layer
  last : Snoc Job → Job → Layer

assemble : Layer → Snoc Job
assemble empty = ε
assemble (last s j) = s ▻ j

g h : Layer → Nat
g empty = 0
g (last s j) = penalty (elapsed s) j
h empty = 0
h (last s j) = cost s

private
  swap : ∀ a b → max a b ≡ max b a
  swap 0 0 = refl
  swap 0 (suc b) = refl
  swap (suc a) 0 = refl
  swap (suc a) (suc b) = cong suc (swap a b)

factor : ∀ t → cost (assemble t) ≡ max (g t) (h t)
factor empty = refl
factor (last s j) = begin
  cost (s ▻ j) ≡⟨⟩
  max (cost s) (penalty (elapsed s) j) ≡⟨ swap (cost s) (penalty (elapsed s) j) ⟩
  max (g (last s j)) (h (last s j)) ∎
