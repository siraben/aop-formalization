{-# OPTIONS --safe --without-K #-}
module AoP.TeXNearestReading where

open import AoP.Prelude
open import AoP.TeXRoundInterval using (module Decimal)
open import AoP.TeXRenderedNearest using (module At)
open import AoP.TeXClosestShortest using (error; scale; numerator)
open import AoP.TeXDistanceScale using (width; power)
open import AoP.TeXExternal using (length)
open import AoP.TeXFixedWidthUnique using (numerator-bound)
open import AoP.TeXFraction using (Digit; intern)
open import AoP.FractionCrossOrder using (module Arithmetic)
open import AoP.NatOrder using (_≤_; s≤)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

-- At a known width, the closed integer range and the decoder describe
-- exactly the same candidates. Thus the renderer's optimum compares
-- directly to every digit list at that width, including leading zeroes.
module Reading (t k h : Nat) (endpoint : suc (suc (suc (t * 2))) * power k ≡ suc h) where
  lo = suc (t * 2)
  module A = At k (lo * power k) h (suc t * power k)
  module R = A.S.R
  cap : ∀ v n → suc n ≤ v → n ≤ A.pred v
  cap (suc v) n (s≤ le) = le
  into : ∀ ds → length ds ≡ k → intern ds ≡ suc t → R.Exactly (numerator ds)
  into ds len ok = shift (scale ds) (width ds ∙ cong power len) (Decimal.into t ds ok) (numerator-bound ds)
    where
    open import AoP.TeXGridStop using (InCell)
    shift : ∀ v → v ≡ power k → InCell 131072 (lo * v) (suc (suc lo) * v) (numerator ds) → suc (numerator ds) ≤ v → R.Exactly (numerator ds)
    shift .(power k) refl c small = change _ endpoint c , cap (power k) _ small
      where change : ∀ H → H ≡ suc h → InCell 131072 (lo * power k) H (numerator ds) → InCell 131072 (lo * power k) (suc h) (numerator ds)
            change .(suc h) refl x = x
  out : ∀ ds → length ds ≡ k → R.Exactly (numerator ds) → intern ds ≡ suc t
  out ds len ok = Decimal.out t ds (shift (scale ds) (width ds ∙ cong power len))
    where open import AoP.TeXGridStop using (InCell)
          shift : ∀ v → v ≡ power k → InCell 131072 (lo * v) (suc (suc lo) * v) (numerator ds)
          shift .(power k) refl rewrite endpoint = fst ok
  score : ∀ ds → length ds ≡ k → error (suc t) ds ≡ A.S.cost (numerator ds)
  score ds len = cong (λ v → AoP.TeXNearestNeighbours.err (numerator ds * 65536) (suc t * v)) (width ds ∙ cong power len)
    where import AoP.TeXNearestNeighbours
