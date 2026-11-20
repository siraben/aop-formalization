{-# OPTIONS --safe --without-K #-}
module AoP.AdditionReflection where

open import AoP.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import AoP.NatOrder using (_≤_; s≤)
open import AoP.Relations hiding (cancel)
open import AoP.Shunting using (graph)

-- Exercise 7.33. For a fixed left summand a, pull the comparison
-- relation back along b ↦ a + b. Stripping the same a successors
-- from both sides reflects the comparison to the original arguments.
cancel : ∀ a {b c} → a + b ≤ a + c → b ≤ c
cancel zero p = p
cancel (suc a) (s≤ p) = cancel a p

shift : Nat → Nat ← Nat
shift a = graph (a +_)

reflect : ∀ a → (shift a ˘) ∘ _≤_ ∘ shift a ⊆ _≤_
reflect a (_ , refl , _ , p , refl) = cancel a p

Less : Nat ← Nat
Less b c = suc b ≤ c

cancel-strict : ∀ a {b c} → Less (a + b) (a + c) → Less b c
cancel-strict zero p = p
cancel-strict (suc a) (s≤ p) = cancel-strict a p

reflect-strict : ∀ a → (shift a ˘) ∘ Less ∘ shift a ⊆ Less
reflect-strict a (_ , refl , _ , p , refl) = cancel-strict a p
