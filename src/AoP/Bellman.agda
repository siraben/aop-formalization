{-# OPTIONS --safe --without-K #-}
module AoP.Bellman where

open import AoP.Prelude
open import AoP.Thinning using (Min)

-- §9.1: the principle of optimality for a choice of unary subproblems.
-- A parent first chooses a branch, then inherits a solution of that
-- child. Branches need not agree on how they compute the parent cost.
module Choices {I V : Set} (_≤_ : V → V → Set)
               (trans : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c)
               (child : I → V → Set) (extend : I → V → V)
               (mono : ∀ i {u v} → u ≤ v → extend i u ≤ extend i v) where

  Feasible : V → Set
  Feasible v = Σ I λ i → Σ V λ u → child i u × (extend i u ≡ v)

  -- Instead of storing all feasible costs per child, store one minimum.
  module Table (best : I → V) (optimal : ∀ i → Min _≤_ (best i) (child i)) where
    Reduced : V → Set
    Reduced v = Σ I λ i → extend i (best i) ≡ v

    feasible : ∀ {v} → Reduced v → Feasible v
    feasible (i , eq) = i , best i , fst (optimal i) , eq

    -- The key calculation: m ≤ extend i (best i) ≤ extend i u.
    -- The first inequality uses the parent minimum; the second uses
    -- monotonicity and the child table's optimality invariant.
    bellman : ∀ {m} → Min _≤_ m Reduced → Min _≤_ m Feasible
    bellman (chosen , least) = feasible chosen , λ where
      _ (i , u , valid , refl) →
        trans (least (extend i (best i)) (i , refl))
              (mono i (snd (optimal i) u valid))
