{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.HalvingRun where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; rid; weaken; z≤; s≤; chain)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; false; true)

-- Exercise 6.11. The exponentiation and modulus recurrences both
-- consume the low bit and recurse on the quotient by two. A positive
-- input strictly decreases. Fuel bounds the input; zero fuel therefore
-- never forces a default answer on a positive input.
half : Nat → Nat
half zero = 0
half (suc zero) = 0
half (suc (suc n)) = suc (half n)

low : Nat → Bool
low zero = false
low (suc zero) = true
low (suc (suc n)) = low n

smaller : ∀ n → half (suc n) ≤ n
smaller zero = z≤
smaller (suc zero) = s≤ z≤
smaller (suc (suc n)) = s≤ (weaken (smaller n))

module Run {A : Set} (base : A) (step : Bool → A → A) where
  eval : ∀ fuel n → n ≤ fuel → A
  eval _ zero _ = base
  eval (suc fuel) (suc n) (s≤ p) = step (low (suc n)) (eval fuel (half (suc n)) (chain (smaller n) p))

  solve : Nat → A
  solve n = eval n n (rid n)

  agree : ∀ k l n (p : n ≤ k) (q : n ≤ l) → eval k n p ≡ eval l n q
  agree k l zero p q = refl
  agree (suc k) (suc l) (suc n) (s≤ p) (s≤ q) = cong (step (low (suc n)))
    (agree k l (half (suc n)) (chain (smaller n) p) (chain (smaller n) q))

  recurrence : ∀ n → solve (suc n) ≡ step (low (suc n)) (solve (half (suc n)))
  recurrence n = cong (step (low (suc n))) (agree n _ _ (chain (smaller n) (rid n)) (rid _))

  unique : (f : Nat → A) → f 0 ≡ base →
           (∀ n → f (suc n) ≡ step (low (suc n)) (f (half (suc n)))) → ∀ n → f n ≡ solve n
  unique f stop next n = bounded n n (rid n)
    where
    bounded : ∀ k m (p : m ≤ k) → f m ≡ eval k m p
    bounded k zero p = stop
    bounded (suc k) (suc m) (s≤ p) = next m ∙ cong (step (low (suc m))) (bounded k _ (chain (smaller m) p))
