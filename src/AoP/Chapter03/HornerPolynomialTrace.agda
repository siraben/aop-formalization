{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.HornerPolynomialTrace where

open import AoP.Common.Prelude
open import AoP.Chapter02.Folds using (⦅_∣_⦆)
open import AoP.Chapter03.Horner using (tri; map; module Ruby)
open import AoP.Chapter04.FractionCrossOrder using (module Arithmetic)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

-- §3.2. Coefficients run from constant term to highest degree. The
-- triangle multiplies each coefficient once for every preceding cell.
module At (x : Nat) where
  scale : Nat → Nat
  scale a = a * x
  module R = Ruby 0 _+_ scale refl (λ a b → Arithmetic.sym (Arithmetic.dist a b x))
  eval = ⦅ 0 ∣ (λ a r → a + scale r) ⦆
  correct : ∀ as → R.reduce (tri scale as) ≡ eval as
  correct = R.horner

open At 10
coeffs = 2 ∷ 3 ∷ 4 ∷ []
triangle : tri scale coeffs ≡ 2 ∷ 30 ∷ 400 ∷ []
triangle = begin
  tri scale coeffs ≡⟨⟩
  2 ∷ map scale (3 ∷ map scale (4 ∷ [])) ≡⟨⟩
  2 ∷ map scale (3 ∷ 40 ∷ []) ≡⟨⟩
  2 ∷ 30 ∷ 400 ∷ [] ∎

-- The fused route stores just the evaluated suffix: 4, then 43, then
-- 432. Promotion is justified for every input by distributivity above.
fused : R.reduce (tri scale coeffs) ≡ 432
fused = begin
  R.reduce (tri scale coeffs) ≡⟨ correct coeffs ⟩
  eval coeffs ≡⟨⟩
  2 + scale (3 + scale (4 + scale 0)) ≡⟨⟩
  2 + scale (3 + scale 4) ≡⟨⟩
  2 + scale 43 ≡⟨⟩
  432 ∎
