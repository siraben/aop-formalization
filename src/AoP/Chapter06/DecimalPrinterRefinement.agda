{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.DecimalPrinterRefinement where

open import AoP.Common.Prelude
open import AoP.Chapter01.DecimalDigits
open import AoP.Chapter06.DecimalAccumulator using (printer; read-from; round-trip; StartsPositive; starts; no-leading-zero)
open import AoP.Chapter06.DecimalDivision using (tens)
open import AoP.Chapter01.PositiveFold using (Positive; decode; encode; round-nat; round-positive)
open import AoP.Chapter06.DecimalConverseStep using (Reads)
import AoP.Chapter01.DecimalInverse as Inverse
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- §6.1. Connect the quotient-based list printer to the positive snoc
-- datatype used in the inverse specification. Parsing starts with a
-- nonzero digit; every remaining digit extends an already legal prefix.
grow : Digits → List Digit → Digits
grow prefix [] = prefix
grow prefix (d ∷ ds) = grow (append prefix d) ds
parse : ∀ {ds} → StartsPositive ds → Digits
parse (starts d ds) = grow (first d) ds

private
  ten : ∀ n → n * 10 ≡ tens n
  ten 0 = refl
  ten (suc n) = cong (10 +_) (ten n)
  advance : ∀ p d → magnitude (scale p d) ≡ tens (magnitude p) + value d
  advance p d = shift p d ∙ cong (λ k → 10 + (k + value d)) (ten (decode p))

read-grow : ∀ prefix ds → magnitude (eval (grow prefix ds)) ≡ read-from (magnitude (eval prefix)) ds
read-grow prefix [] = refl
read-grow prefix (d ∷ ds) = read-grow (append prefix d) ds ∙ cong (λ k → read-from k ds) (advance (eval prefix) d)
read-parse : ∀ {ds} (p : StartsPositive ds) → magnitude (eval (parse p)) ≡ read-from 0 ds
read-parse (starts d ds) = read-grow (first d) ds ∙ cong (λ k → read-from (suc k) ds) (round-nat (index d))

-- The accumulator's existing proofs discharge both obligations: its
-- first digit is nonzero and its whole output reads back to the input.
decimal : Nat → Digits
decimal n = parse (no-leading-zero n)
refines : ∀ n → magnitude (eval (decimal n)) ≡ suc n
refines n = read-parse (no-leading-zero n) ∙ round-trip (suc n)

positive : ∀ p → Reads (decimal (decode p)) p
positive p = sym (round-positive _) ∙ cong encode (drop-suc (refines (decode p))) ∙ round-positive p
  where
    sym : ∀ {x y : Positive} → x ≡ y → y ≡ x
    sym refl = refl
    drop-suc : ∀ {x y} → suc x ≡ suc y → x ≡ y
    drop-suc refl = refl

-- Equality of valuations forces equality of canonical digit trees:
-- reprint both values with the Chapter 1 inverse. Consequently the
-- quotient algorithm and the successor algorithm agree digit for digit.
agrees : ∀ p → decimal (decode p) ≡ Printer.decimal Inverse.printer p
agrees p = reverse (Inverse.prints (Inverse.all (decimal (decode p)))) ∙ cong (Printer.decimal Inverse.printer) (positive p)
  where reverse : ∀ {x y : Digits} → x ≡ y → y ≡ x
        reverse refl = refl

prints-back : ∀ ds → decimal (decode (eval ds)) ≡ ds
prints-back ds = agrees (eval ds) ∙ Inverse.prints (Inverse.all ds)

quotient-printer : Printer
Printer.decimal quotient-printer p = decimal (decode p)
Printer.reads-back quotient-printer = positive
Printer.prints-back quotient-printer = prints-back
