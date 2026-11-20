{-# OPTIONS --safe --without-K #-}
module AoP.GuardLoss where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; rid; z≤)
open import AoP.Thinning using (Thin)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 8.22. Minimize the state. Starting from either 0 or 1,
-- keep only 0; this is locally valid thinning. Both branch functions
-- return their input, but both require a positive input. After expansion
-- the full search can return 1 and the pruned search has no result.
data Pool : Nat → Set where
  zero : Pool 0
  one : Pool 1
Only : Nat → Set
Only x = x ≡ 0
initial : Thin _≤_ Only Pool
Thin.subset initial refl = zero
Thin.cover initial _ zero = 0 , refl , rid 0
Thin.cover initial _ one = 0 , refl , z≤

data Branch : Nat → Nat → Set where
  left right : ∀ {n} → 1 ≤ n → Branch n n
Next : (Nat → Set) → Nat → Set
Next X n = Σ Nat λ m → X m × Branch n m
full : Next Pool 1
full = 1 , one , left (rid 1)
empty : ∀ {n} → Next Only n → ⊥
empty (_ , refl , left ())
empty (_ , refl , right ())
failed : Thin _≤_ (Next Only) (Next Pool) → ⊥
failed th with Thin.cover th 1 full
... | n , result , bound = empty result
