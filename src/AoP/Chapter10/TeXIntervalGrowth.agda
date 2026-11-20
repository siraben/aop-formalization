{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXIntervalGrowth where

open import AoP.Common.Prelude
open import AoP.Chapter04.FractionCrossOrder using (module Arithmetic)
open Arithmetic using (dist)
open import AoP.Chapter10.TeXFivePlaces using (five)
open import AoP.Chapter10.TeXGridStop using (InCell)
open import AoP.Chapter10.OpenUpperDigit using (Upper)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- For every positive target n, the initial upper numerator is two
-- above the lower numerator. Each emitted place multiplies both by
-- ten. Track this width without unfolding five products of an unknown L.
scale : Nat → Nat → Nat
scale 0 x = x
scale (suc k) x = scale k x * 10
spread : ∀ k a b → scale k (a + b) ≡ scale k a + scale k b
spread 0 a b = refl
spread (suc k) a b = cong (_* 10) (spread k a b) ∙ dist (scale k a) (scale k b) 10

at-five : ∀ L z → Upper 131072 (scale 5 (2 + L)) z → InCell 131072 (scale 5 L) (scale 5 (2 + L)) z
at-five L z = transport (scale 5 L) (scale 5 (2 + L)) z (spread 5 2 L)
  where
  transport : ∀ l h t → h ≡ 200000 + l → Upper 131072 h t → InCell 131072 l h t
  transport l .(200000 + l) t refl = five l t
