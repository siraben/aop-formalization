{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.ModulusBound where

open import Agda.Builtin.Nat using (Nat; zero; suc; _-_)
open import Agda.Builtin.Bool using (false; true)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; weaken; chain)
open import AoP.Chapter06.HalvingDigits using (double; shift)
open import AoP.Common.Prelude

-- §6.4. For divisor b = k+1 a stored remainder r is at most k.
-- Shifting in one bit can produce at most 2k+1. Consequently, if
-- the shifted value reaches b, subtracting b just once restores the
-- invariant. Equality with b belongs to the subtraction branch.
mono : ∀ {a k} → a ≤ k → double a ≤ double k
mono {k = zero} z≤ = z≤
mono {k = suc k} z≤ = z≤
mono (s≤ p) = s≤ (s≤ (mono p))

shift-bound : ∀ bit {r k} → r ≤ k → shift bit r ≤ suc (double k)
shift-bound false p = weaken (mono p)
shift-bound true p = s≤ (mono p)

private
  minus-step : ∀ n k → (n - k) ≤ suc ((n - suc k))
  minus-step zero zero = z≤
  minus-step zero (suc k) = z≤
  minus-step (suc n) zero = s≤ (refl≤ n)
    where refl≤ : ∀ m → m ≤ m
          refl≤ zero = z≤
          refl≤ (suc m) = s≤ (refl≤ m)
  minus-step (suc n) (suc k) = minus-step n k

  cut : ∀ k n → n ≤ double k → (n - k) ≤ k
  cut zero .0 z≤ = z≤
  cut (suc k) zero p = z≤
  cut (suc k) (suc zero) p = zero-minus k
    where zero-minus : ∀ i → (0 - i) ≤ suc i
          zero-minus zero = z≤
          zero-minus (suc i) = z≤
  cut (suc k) (suc (suc n)) (s≤ (s≤ p)) = next n k (cut k n p)
    where next : ∀ m i → (m - i) ≤ i → (suc m - i) ≤ suc i
          next m zero h = s≤ h
          next m (suc i) h = chain (minus-step m i) (s≤ h)

reduced : ∀ k n → n ≤ suc (double k) → (n - suc k) ≤ k
reduced k zero p = z≤
reduced k (suc n) (s≤ p) = cut k n p
