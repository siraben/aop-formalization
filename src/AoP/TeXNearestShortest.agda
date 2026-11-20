{-# OPTIONS --safe --without-K #-}
module AoP.TeXNearestShortest where

open import AoP.Prelude
open import AoP.TeXNearestReading using (module Reading)
open import AoP.TeXFraction using (Digit; intern)
open import AoP.TeXExternal using (Shortest; length; shortest)
open import AoP.TeXClosestShortest using (Closest; winner; error; numerator)
open import AoP.TeXDistanceScale using (power)
open import AoP.FractionCrossOrder using (module Arithmetic)
open import AoP.NatOrder using (_≤_)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

-- A shortest certificate supplies both a width and a feasible witness
-- for the clamp. Every same-width rival passes through the decoder bridge.
module Improve (t : Nat) (base : List Digit) (opt : Shortest (suc t) base) where
  k = length base
  hi = suc (suc (suc (t * 2)))
  positive : ∀ n → Σ Nat (λ m → power n ≡ suc m)
  positive 0 = 0 , refl
  positive (suc n) with positive n
  ... | m , eq = _ , (cong (10 *_) eq ∙ Arithmetic.step 10 m)
  endpoint : Σ Nat (λ h → hi * power k ≡ suc h)
  endpoint with positive k
  ... | m , eq = _ , (cong (hi *_) eq ∙ Arithmetic.step hi m)
  module R = Reading t k (fst endpoint) (snd endpoint)
  opaque
    r : R.A.Result
    r = R.A.solve (numerator base) (R.into base refl (Shortest.round-trip opt))
  open R.A.Result r
  readback = R.out ds at-width admissible
  shortest′ : Shortest (suc t) ds
  shortest′ = shortest readback λ es yes → transport at-width (Shortest.minimal opt es yes)
    where transport : ∀ {a b c} → a ≡ b → b ≤ c → a ≤ c
          transport refl p = p
  certified : Closest (suc t) ds
  certified = winner shortest′ λ es ok eq → compare-error es ok (eq ∙ at-width)
    where compare-error : ∀ es → intern es ≡ suc t → length es ≡ k → error (suc t) ds ≤ error (suc t) es
          compare-error es ok len = transport (R.score ds at-width) (R.score es len) (minimum (numerator es) (R.into es len ok))
            where transport : ∀ {a b c d : Nat} → a ≡ b → c ≡ d → b ≤ d → a ≤ c
                  transport refl refl p = p
  solution : Σ (List Digit) (Closest (suc t))
  solution = ds , certified
