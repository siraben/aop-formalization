{-# OPTIONS --safe --without-K #-}
module AoP.Bracketing where

open import AoP.Prelude
open import AoP.Trees using (Tree; tip; bin; foldt)
open import AoP.Naturality using (_++_)
open import Agda.Builtin.Nat using (Nat; _+_)
open import AoP.NatOrder using (_≤_; rid; sum-mono)

-- §9.3. Parentheses can change the cost without changing the answer.
-- Concatenating lists of lengths 2, 3, 4 costs 2 + 5 with left grouping
-- but 3 + 2 with right grouping: append traverses its left input. A tree
-- encodes a bracketing, and its leaves in order specify its input. An
-- interval solver must therefore compare trees with the *same leaves*.
module Model {A Size : Set} (atom : A → Size) (combine : Size → Size → Size)
             (charge : Size → Size → Nat) where
  leaves : Tree A → List A
  leaves = foldt (λ a → a ∷ []) _++_

  size : Tree A → Size
  size = foldt atom combine

  cost : Tree A → Nat
  cost (tip _) = 0
  cost (bin l r) = charge (size l) (size r) + (cost l + cost r)

  -- This is the context hypothesis from the book, factored out of the
  -- monotonicity calculation: size is determined by the input sequence.
  module OptimalSubtrees (same-size : ∀ l r → leaves l ≡ leaves r → size l ≡ size r) where
    replace : ∀ l l′ r r′ → leaves l ≡ leaves l′ → leaves r ≡ leaves r′ →
              cost l ≤ cost l′ → cost r ≤ cost r′ → cost (bin l r) ≤ cost (bin l′ r′)
    replace l l′ r r′ eq₁ eq₂ cheap₁ cheap₂ rewrite same-size l l′ eq₁ | same-size r r′ eq₂ =
      sum-mono (rid (charge (size l′) (size r′))) (sum-mono cheap₁ cheap₂)

-- Small executable comparison for list concatenation, with leaf lengths
-- as input labels. This checks the costs, not just the abstract recurrence.
module Append = Model (λ (n : Nat) → n) _+_ (λ l _ → l)
left-cost : Append.cost (bin (bin (tip 2) (tip 3)) (tip 4)) ≡ 7
left-cost = refl
right-cost : Append.cost (bin (tip 2) (bin (tip 3) (tip 4))) ≡ 5
right-cost = refl
