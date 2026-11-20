{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.DecimalGridStep where

open import AoP.Common.Prelude
open import AoP.Chapter03.TeXFraction using (Digit; cshift)
open import AoP.Chapter03.GridTranslation using (Below)
open import AoP.Chapter03.GridDivision using (module Law)
open import AoP.Chapter04.FractionCrossOrder using (module Arithmetic)
open Arithmetic using (sym; comm; dist; switch)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

private
  assoc : ∀ a b c → (a * b) * c ≡ a * (b * c)
  assoc 0 b c = refl
  assoc (suc a) b c rewrite dist b (a * b) c | assoc a b c = refl

-- The new width v is half the old width. Pulling back a threshold
-- through division by ten gives exactly five old blocks per index.
align : ∀ v t → (t * v) * 10 ≡ (t * 5) * (2 * v)
align v t = begin
  (t * v) * 10 ≡⟨ switch t v 10 ⟩
  (t * 10) * v ≡⟨ cong (_* v) (sym (assoc t 5 2)) ⟩
  ((t * 5) * 2) * v ≡⟨ assoc (t * 5) 2 v ⟩
  (t * 5) * (2 * v) ∎

step : ∀ v m → m * (2 * v) ≡ 131072 → ∀ d {x y} → Below (2 * v) x y → Below v (cshift d x) (cshift d y)
step v m multiple d {x} {y} h = transfer ((m * a) * w) (131072 * a) offset proof
  where
  w = 2 * v
  a = Digit.numeral d
  open Law 9 w v (_* 5) (align v)
  offset : (m * a) * w ≡ 131072 * a
  offset = switch m a w ∙ cong (_* a) multiple
  proof = digit-step (m * a) h
  transfer : ∀ u z → u ≡ z → Below v (quot (u + x)) (quot (u + y)) → Below v (quot (z + x)) (quot (z + y))
  transfer u .u refl p = p
