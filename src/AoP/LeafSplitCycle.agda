{-# OPTIONS --safe --without-K #-}
module AoP.LeafSplitCycle where

open import AoP.Prelude
open import AoP.Naturality using (_++_)
open import AoP.Inductive using (Acc; acc)
open import AoP.Complement using (⊥)

-- Exercise 6.29. A sorted split may still loop: the cross-child
-- comparison is vacuous for an empty left child. Even a split policy
-- reserving singletons as base cases can return the entire two-key
-- input as its right child. Such a recursive dependency is inaccessible.
module Law {A : Set} (R : A → A → Set) where
  open import AoP.Subsequences using (_∈_)
  data Child : List A → List A → Set where
    right : ∀ l r → (∀ {a b} → a ∈ l → b ∈ r → R a b) → Child r (l ++ r)
  loop : ∀ x y → Child (x ∷ y ∷ []) (x ∷ y ∷ [])
  loop x y = right [] (x ∷ y ∷ []) (λ ())

  private
    cycle : ∀ {xs} → Child xs xs → Acc Child xs → ⊥
    cycle edge (acc smaller) = cycle edge (smaller _ edge)
  inaccessible : ∀ x y → Acc Child (x ∷ y ∷ []) → ⊥
  inaccessible x y = cycle (loop x y)
