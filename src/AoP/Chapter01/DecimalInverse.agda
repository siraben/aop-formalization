{-# OPTIONS --safe --without-K #-}
module AoP.Chapter01.DecimalInverse where

open import AoP.Common.Prelude
open import AoP.Chapter01.DecimalDigits
open import AoP.Chapter01.DecimalSuccessor

-- To prove that printing recovers the original digits, show that every
-- canonical numeral occurs in the count from one. Appending a zero to
-- consecutive prefixes separates the resulting numbers by ten increments.
data Reached : Digits → Set where
  start : Reached (first one)
  advance : ∀ {ds} → Reached ds → Reached (inc ds)

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import AoP.Chapter01.Naturals using (foldn)

steps : ∀ n {ds} → Reached ds → Reached (foldn ds inc n)
steps zero r = r
steps (suc n) r = advance (steps n r)

leading : ∀ d → Reached (first d)
leading one = start
leading two = steps 1 start
leading three = steps 2 start
leading four = steps 3 start
leading five = steps 4 start
leading six = steps 5 start
leading seven = steps 6 start
leading eight = steps 7 start
leading nine = steps 8 start

zero-place : ∀ {ds} → Reached ds → Reached (append ds oh)
zero-place start = advance (leading nine)
zero-place (advance r) = steps 10 (zero-place r)

units : ∀ ds → Reached (append ds oh) → ∀ d → Reached (append ds (nonzero d))
units ds r one = advance r
units ds r two = steps 2 r
units ds r three = steps 3 r
units ds r four = steps 4 r
units ds r five = steps 5 r
units ds r six = steps 6 r
units ds r seven = steps 7 r
units ds r eight = steps 8 r
units ds r nine = steps 9 r

all : ∀ ds → Reached ds
all (first d) = leading d
all (append ds oh) = zero-place (all ds)
all (append ds (nonzero d)) = units ds (zero-place (all ds)) d

prints : ∀ {ds} → Reached ds → print (eval ds) ≡ ds
prints start = refl
prints (advance {ds} r) = begin
  print (eval (inc ds)) ≡⟨ cong print (inc-law ds) ⟩
  inc (print (eval ds)) ≡⟨ cong inc (prints r) ⟩
  inc ds ∎

printer : Printer
Printer.decimal printer = print
Printer.reads-back printer = reads
Printer.prints-back printer ds = prints (all ds)
