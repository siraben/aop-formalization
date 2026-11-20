{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.HalvingPower where

open import AoP.Common.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; false; true)
open import AoP.Chapter06.HalvingDigits using (double; shift; module Fuse)
open import AoP.Chapter06.Squaring using (module Powers)

-- §6.4. Run the halving recurrence directly on a natural exponent.
-- The even case squares the recursively computed power. An odd low
-- bit contributes one more copy of the base, on the left. The step
-- follows from x^(n+n) = x^n · x^n; no commutativity is required.
private
  slide : ∀ n m → suc (n + m) ≡ n + suc m
  slide zero m = refl
  slide (suc n) m = cong suc (slide n m)

  twice : ∀ n → double n ≡ n + n
  twice zero = refl
  twice (suc n) = cong (λ k → suc (suc k)) (twice n) ∙ cong suc (slide n n)

module Fast {M : Set} (e : M) (_·_ : M → M → M) (unit : ∀ u → e · u ≡ u)
            (assoc : ∀ u v w → (u · v) · w ≡ u · (v · w)) (x : M) where
  open Powers e _·_ unit assoc x using (power; add; square)
  step : Bool → M → M
  step false u = square u
  step true u = x · square u

  even : ∀ n → power (double n) ≡ square (power n)
  even n = cong power (twice n) ∙ add n n

  digit : ∀ b n → power (shift b n) ≡ step b (power n)
  digit false n = even n
  digit true n = cong (x ·_) (even n)

  module F = Fuse power step digit
  fast = F.H.solve
  correct : ∀ n → power n ≡ fast n
  correct = F.correct
