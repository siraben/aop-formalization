{-# OPTIONS --safe --without-K #-}
module AoP.HalvingDigits where

open import AoP.Prelude
open import AoP.HalvingRun using (half; low; module Run)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; false; true)

-- §6.4. To recover the input of a binary digit step, double the
-- quotient and add the low bit. The proof peels off two successors:
-- this increases the quotient by one without changing the bit.
double : Nat → Nat
double zero = zero
double (suc n) = suc (suc (double n))

shift : Bool → Nat → Nat
shift false n = double n
shift true n = suc (double n)

advance : ∀ b n → shift b (suc n) ≡ suc (suc (shift b n))
advance false n = refl
advance true n = refl

reconstruct : ∀ n → shift (low n) (half n) ≡ n
reconstruct zero = refl
reconstruct (suc zero) = refl
reconstruct (suc (suc n)) = begin
  shift (low n) (suc (half n)) ≡⟨ advance (low n) (half n) ⟩
  suc (suc (shift (low n) (half n))) ≡⟨ cong suc (cong suc (reconstruct n)) ⟩
  suc (suc n) ∎

-- Fusion in the useful direction: supply an interpretation and its
-- digit law. The generic halving program then computes that very
-- interpretation directly from a natural, without allocating digits.
module Fuse {A : Set} (value : Nat → A) (step : Bool → A → A)
            (digit-law : ∀ b n → value (shift b n) ≡ step b (value n)) where
  module H = Run (value 0) step
  correct : ∀ n → value n ≡ H.solve n
  correct = H.unique value refl λ n → begin
    value (suc n) ≡⟨ cong value (back (reconstruct (suc n))) ⟩
    value (shift (low (suc n)) (half (suc n))) ≡⟨ digit-law _ _ ⟩
    step (low (suc n)) (value (half (suc n))) ∎
    where back : ∀ {a b : Nat} → a ≡ b → b ≡ a
          back refl = refl
