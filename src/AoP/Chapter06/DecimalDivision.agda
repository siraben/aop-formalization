{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.DecimalDivision where

open import AoP.Common.Prelude
open import AoP.Chapter01.DecimalDigits using (Digit; Nonzero; oh; nonzero; one; two; three; four; five; six; seven; eight; nine; value)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

-- §6.1. The index is the dividend: a split supplies its decimal
-- quotient and a digit, certifying n = 10 q + d by construction.
-- Crossing a group of ten only increments q; the low digit survives.
tens : Nat → Nat
tens zero = 0
tens (suc q) = 10 + tens q

data Split : Nat → Set where
  parts : (q : Nat) (d : Digit) → Split (tens q + value d)

split : ∀ n → Split n
split 0 = parts 0 oh
split 1 = parts 0 (nonzero one)
split 2 = parts 0 (nonzero two)
split 3 = parts 0 (nonzero three)
split 4 = parts 0 (nonzero four)
split 5 = parts 0 (nonzero five)
split 6 = parts 0 (nonzero six)
split 7 = parts 0 (nonzero seven)
split 8 = parts 0 (nonzero eight)
split 9 = parts 0 (nonzero nine)
split (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n)))))))))) with split n
... | parts q d = parts (suc q) d

carry-example : split 100 ≡ parts 10 oh
carry-example = refl
