{-# OPTIONS --safe --without-K #-}
module AoP.Chapter01.ArithmeticFolds where

open import AoP.Common.Prelude
open import AoP.Chapter01.Naturals using (foldn)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- §1.2. Fix the first argument; the second counts iterations. Thus
-- 3⁴ applies “multiply by three” four times, starting at one.
plus times power : Nat → Nat → Nat
plus m = foldn m suc
times m = foldn 0 (plus m)
power m = foldn 1 (times m)

plus-step : ∀ m n → plus m (suc n) ≡ suc (plus m n)
plus-step m n = refl
times-step : ∀ m n → times m (suc n) ≡ plus m (times m n)
times-step m n = refl
power-step : ∀ m n → power m (suc n) ≡ times m (power m n)
power-step m n = refl

three-to-four : power 3 4 ≡ 81
three-to-four = refl

-- The unrestricted equation f(n) = f(n+1) admits every constant.
-- Conversely, induction takes each value back to the value at zero.
Stable : (Nat → Nat) → Set
Stable f = ∀ n → f n ≡ f (suc n)

constant : ∀ c → Stable (λ _ → c)
constant c n = refl

all-constant : ∀ f → Stable f → ∀ n → f zero ≡ f n
all-constant f law zero = refl
all-constant f law (suc n) = begin
  f zero    ≡⟨ all-constant f law n ⟩
  f n       ≡⟨ law n ⟩
  f (suc n) ∎
