{-# OPTIONS --safe --without-K #-}
module AoP.TeXFixedWidthUnique where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; z≤; s≤; rid; chain; sum-mono)
open import AoP.DigitInterval using (Cell; unique)
open import AoP.TeXClosestShortest using (scale; numerator)
open import AoP.TeXDistanceScale using (width; power)
open import AoP.TeXFraction using (Digit; digit)
open import AoP.TeXExternal using (length)
open import AoP.FractionCrossOrder using (module Arithmetic)
open Arithmetic using (move; sym)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

private
  plus : ∀ x y → x + y ≡ y + x
  plus 0 y = sym (Arithmetic.unit y)
  plus (suc x) y = cong suc (plus x y) ∙ sym (move y x)
  pad : ∀ a b → a ≤ a + b
  pad 0 b = z≤
  pad (suc a) b = s≤ (pad a b)
  end : ∀ a v t → suc t ≤ v → suc (a * v + t) ≤ suc a * v
  end a v t h rewrite sym (move (a * v) t) | plus v (a * v) = sum-mono (rid _) h
  below : ∀ ds → suc (numerator ds) ≤ scale ds
  below [] = rid 1
  below (d ∷ ds) = chain (end (Digit.numeral d) (scale ds) (numerator ds) (below ds)) (Arithmetic.scale (scale ds) (s≤ (Digit.valid d)))
  head-cell : ∀ a ds → Cell (scale ds) (a * scale ds + numerator ds) a
  head-cell a ds = pad _ _ , end a (scale ds) (numerator ds) (below ds)
  inj : ∀ {a b} → suc a ≡ suc b → a ≡ b
  inj refl = refl
  cancel : ∀ a {b c} → a + b ≡ a + c → b ≡ c
  cancel 0 h = h
  cancel (suc a) h = cancel a (inj h)
  proof : ∀ {a b} (p q : a ≤ b) → p ≡ q
  proof z≤ z≤ = refl
  proof (s≤ p) (s≤ q) = cong s≤ (proof p q)
  cell-eq : ∀ {v u n m a} → v ≡ u → n ≡ m → Cell v n a → Cell u m a
  cell-eq refl refl h = h

numerator-bound : ∀ ds → suc (numerator ds) ≤ scale ds
numerator-bound = below

-- Width matters: .01 and .1 have the same numerator but different widths.
recover : ∀ ds es → length ds ≡ length es → numerator ds ≡ numerator es → ds ≡ es
recover [] [] _ _ = refl
recover (digit a p ∷ ds) (digit b q ∷ es) lengths nums with unique (scale es) (numerator (digit b q ∷ es)) a b (cell-eq {a = a} (width ds ∙ cong power (inj lengths) ∙ sym (width es)) nums (head-cell a ds)) (head-cell b es)
... | refl with proof p q
...   | refl = cong (digit a p ∷_) (recover ds es (inj lengths) (cancel (a * scale es) (cong (λ v → a * v + numerator ds) (width es ∙ cong power (sym (inj lengths)) ∙ sym (width ds)) ∙ nums)))
