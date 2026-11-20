{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXResidualGap where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; s≤; z≤)
open import AoP.Chapter04.FractionCrossOrder using (module Arithmetic)
open Arithmetic using (dist; sym; move)
open import AoP.Chapter10.TeXPrinterStep using (module Emit)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_; _-_)

-- While the lower residual is positive, subtraction clips neither
-- endpoint. Their separation grows by ten on each nonterminal step.
private
  peel : ∀ a b c g r → a - c ≡ suc r → a + g ≤ b → suc r + g ≤ b - c
  peel a b 0 g r refl h = h
  peel 0 b (suc c) g r ()
  peel (suc a) (suc b) (suc c) g r eq (s≤ h) = peel a b c g r eq h
  peel (suc a) 0 (suc c) g r eq ()

module Next (k j p : Nat) (bound : suc j ≤ suc k) where
  module E = Emit k j 0 p bound
  gap : ∀ g r → p + g ≤ suc j → E.low ≡ suc r → suc r + g * 10 ≤ E.high
  gap g r h eq = peel (p * 10) (suc j * 10) (E.d * suc k) (g * 10) r eq scaled
    where
    scaled : p * 10 + g * 10 ≤ suc j * 10
    scaled rewrite sym (dist p g 10) = Arithmetic.scale 10 h
