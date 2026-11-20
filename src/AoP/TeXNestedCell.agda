{-# OPTIONS --safe --without-K #-}
module AoP.TeXNestedCell where

open import AoP.Prelude
open import AoP.DigitInterval using (Cell)
open import AoP.NatOrder using (_≤_; z≤; s≤; rid; chain; sum-mono)
open import AoP.FractionCrossOrder using (module Arithmetic)
open Arithmetic using (dist; assoc; sym; move; swap)
open import Agda.Builtin.Nat using (Nat; suc; _*_; _+_)

-- A suffix numerator N has integer part s when divided by v.
-- Add an integer digit contribution a, then divide by ten. The two
-- floor operations compose to a single cell at denominator 10v.
private
  mul : ∀ v {x y} → x ≤ y → x * v ≤ y * v
  mul v z≤ = z≤
  mul v (s≤ h) = sum-mono (rid v) (mul v h)
  flatten : ∀ a b c → (a * b) * c ≡ a * (b * c)
  flatten 0 b c = refl
  flatten (suc a) b c rewrite dist b (a * b) c | flatten a b c = refl

translate : ∀ v a N s → Cell v N s → Cell v (a * v + N) (a + s)
translate v a N s (lo , hi) rewrite dist a s v | sym (move (a * v) N) | swap v (a * v) (s * v) = sum-mono (rid _) lo , sum-mono (rid _) hi

compose : ∀ v b N s t → Cell v N s → Cell b s t → Cell (b * v) N t
compose v b N s t (lo , hi) (start , end) = lower , upper
  where
  lower : t * (b * v) ≤ N
  lower rewrite sym (flatten t b v) = chain (mul v start) lo
  upper : suc N ≤ suc t * (b * v)
  upper = cast (flatten (suc t) b v) (chain hi (mul v end))
    where cast : ∀ {x y} → x ≡ y → suc N ≤ x → suc N ≤ y
          cast refl h = h
