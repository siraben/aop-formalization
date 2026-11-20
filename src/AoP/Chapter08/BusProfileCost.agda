{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.BusProfileCost where

open import AoP.Common.Prelude
open import AoP.Chapter08.BusProfile
open import AoP.Chapter08.BusWalking using (module Layout)
open import AoP.Common.NatOrder using (_≤_; z≤; sum-mono)
open import AoP.Chapter05.Subsequences using (here; there)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- Index the blocks in the same order as the objective. The passenger
-- count multiplies each distance by a nonnegative natural weight.
indices : Nat → List (Nat × Nat) → List Nat
indices j [] = []
indices j ((0 , 0) ∷ bs) = indices (suc j) bs
indices j ((0 , suc c) ∷ bs) = j ∷ indices (suc j) bs
indices j ((suc b , c) ∷ bs) = j ∷ indices (suc j) bs

weight : ∀ n {x y} → x ≤ y → n * x ≤ n * y
weight 0 le = z≤
weight (suc n) le = sum-mono le (weight n le)

cost : Stops → Nat → List (Nat × Nat) → Nat
cost (sites k ks) = Layout.walking k ks

cost-bound : ∀ j bs l r → Profile (indices j bs) l r → cost l j bs ≤ cost r j bs
cost-bound j [] (sites x xs) (sites y ys) p = z≤
cost-bound j ((0 , 0) ∷ bs) l@(sites x xs) r@(sites y ys) p = cost-bound (suc j) bs l r p
cost-bound j ((0 , suc c) ∷ bs) l@(sites x xs) r@(sites y ys) p =
  sum-mono (weight (suc c) (p j here)) (cost-bound (suc j) bs l r (λ i m → p i (there m)))
cost-bound j ((suc b , c) ∷ bs) l@(sites x xs) r@(sites y ys) p =
  sum-mono (weight (suc b + c) (p j here)) (cost-bound (suc j) bs l r (λ i m → p i (there m)))
