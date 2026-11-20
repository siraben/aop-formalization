{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXLoopRoundTrip where

open import AoP.Common.Prelude
open import AoP.Chapter10.TeXResidualLoop
open import AoP.Chapter10.TeXLoopTermination using (five)
open import AoP.Chapter10.TeXLoopSound using (module Sound)
open import AoP.Chapter10.TeXRoundInterval using (module Decimal)
open import AoP.Chapter03.TeXFraction using (Digit; intern)
open import AoP.Common.NatOrder using (_≤_; rid)
open import AoP.Chapter04.FractionCrossOrder using (module Arithmetic)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- Keep the equality to the actual loop result: existence of some
-- representation alone would also follow from the two-pass printer.
module Positive (t : Nat) (bound : suc (suc (suc (t * 2))) ≤ 131072) where
  lo = suc (t * 2)
  j = suc lo
  result = Loop.run 131071 5 lo j bound
  module S = Sound 131071
  private
    gap : lo + 2 ≤ suc j
    gap rewrite Arithmetic.move lo 1 | Arithmetic.move lo 0 | Arithmetic.unit lo = rid _
    recover : ∀ ds → result ≡ printed ds → intern ds ≡ suc t
    recover ds eq = Decimal.out t ds (change result eq (S.sound 5 lo j bound))
      where change : ∀ r → r ≡ printed ds → S.Good lo (suc j) r → Decimal.Valid t ds
            change .(printed ds) refl h = h
  output : Σ (List Digit) (λ ds → (result ≡ printed ds) × (intern ds ≡ suc t))
  output = finish (five lo j bound gap)
    where finish : Σ (List Digit) (λ ds → result ≡ printed ds) → Σ (List Digit) (λ ds → (result ≡ printed ds) × (intern ds ≡ suc t))
          finish (ds , eq) = ds , (eq , recover ds eq)
