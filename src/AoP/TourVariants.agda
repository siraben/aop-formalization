{-# OPTIONS --safe --without-K #-}
module AoP.TourVariants where

open import AoP.Prelude
open import AoP.Polynomial using (inl; inr)
open import AoP.NatOrder using (_≤_; rid; chain; sum-mono; compare)
open import Agda.Builtin.Nat using (Nat; _+_)

-- Exercises 8.27–8.28. Keep both endpoints fixed. Each interior
-- city still admits the two one-leg assignments. A third choice is
-- either to visit on both legs (7.27) or on neither leg (7.28).
data Mode : Set where both neither : Mode
data Move : Set where out home extra : Move

module Solve {City : Set} (edge : City → City → Nat) (end : City) (mode : Mode) where
  data Route : List City → Set where
    close : Route []
    step : ∀ {x xs} → Move → Route xs → Route (x ∷ xs)

  Next = City × (City × Nat)
  third : Mode → City → City → City → Next
  third both x u v = x , x , (edge u x + edge x v)
  third neither x u v = u , v , 0

  next : Move → City → City → City → Next
  next out x u v = x , v , edge u x
  next home x u v = u , x , edge x v
  next extra x u v = third mode x u v

  cost : ∀ {xs} → City → City → Route xs → Nat
  cost u v close = edge u end + edge end v
  cost u v (step {x} m p) with next m x u v
  ... | a , b , c = c + cost a b p

  Best : City → City → List City → Set
  Best u v xs = Σ (Route xs) λ p → (q : Route xs) → cost u v p ≤ cost u v q

  solve : ∀ xs u v → Best u v xs
  solve [] u v = close , λ { close → rid _ }
  solve (x ∷ xs) u v = winner
    where
    branch : ∀ m → Σ (Route xs) λ p → (q : Route xs) → cost u v (step {x} m p) ≤ cost u v (step {x} m q)
    branch m with next m x u v | solve xs (fst (next m x u v)) (fst (snd (next m x u v)))
    ... | a , b , c | p , opt = p , λ q → sum-mono (rid c) (opt q)
    candidate : Move → Route (x ∷ xs)
    candidate m = step m (fst (branch m))
    price = λ m → cost u v (candidate m)
    winner : Best u v (x ∷ xs)
    winner with compare (price out) (price home) | compare (price out) (price extra) | compare (price home) (price extra)
    ... | inl oh | inl oe | _ = candidate out , λ { (step out q) → snd (branch out) q ; (step home q) → chain oh (snd (branch home) q) ; (step extra q) → chain oe (snd (branch extra) q) }
    ... | inl oh | inr eo | _ = candidate extra , λ { (step out q) → chain eo (snd (branch out) q) ; (step home q) → chain eo (chain oh (snd (branch home) q)) ; (step extra q) → snd (branch extra) q }
    ... | inr ho | _ | inl he = candidate home , λ { (step out q) → chain ho (snd (branch out) q) ; (step home q) → snd (branch home) q ; (step extra q) → chain he (snd (branch extra) q) }
    ... | inr ho | _ | inr eh = candidate extra , λ { (step out q) → chain eh (chain ho (snd (branch out) q)) ; (step home q) → chain eh (snd (branch home) q) ; (step extra q) → snd (branch extra) q }
