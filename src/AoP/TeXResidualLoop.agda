{-# OPTIONS --safe --without-K #-}
module AoP.TeXResidualLoop where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; s≤; z≤)
open import AoP.TeXFraction using (Digit)
open import AoP.TeXPrinterStep using (module Emit)
open import Agda.Builtin.Nat using (Nat; suc)

-- Execute the strict digit rule and stop on the clipped lower residual.
-- Fuel exhaustion is observable, including at the last permitted digit:
-- a zero lower residual succeeds before the loop tests remaining fuel.
data Result : Set where
  exhausted : Result
  printed : List Digit → Result
prepend : Digit → Result → Result
prepend d exhausted = exhausted
prepend d (printed ds) = printed (d ∷ ds)
pred : Nat → Nat
pred 0 = 0
pred (suc j) = j
nonzero : ∀ r → 1 ≤ r → r ≡ suc (pred r)
nonzero (suc r) p = refl
next-bound : ∀ k r → (1 ≤ r) × (r ≤ suc k) → suc (pred r) ≤ suc k
next-bound k (suc r) (_ , b) = b
module Loop (k : Nat) where
  run : ∀ (fuel p j : Nat) → suc j ≤ suc k → Result
  run fuel 0 j bound = printed []
  run 0 (suc p) j bound = exhausted
  run (suc fuel) (suc p) j bound = prepend E.letter (run fuel E.low (pred E.high) (next-bound k E.high E.next-high))
    where module E = Emit k j 0 (suc p) bound

-- One upper endpoint lies exactly at the next digit boundary: with W=10
-- and [p,q)=[4,5), the only printable one-digit fraction is .4.
module Trace where
  open Loop 9
  bound : 5 ≤ 10
  bound = s≤ (s≤ (s≤ (s≤ (s≤ z≤))))
  observe : Result → List Nat
  observe exhausted = []
  observe (printed ds) = numerals ds
    where numerals : List Digit → List Nat
          numerals [] = []
          numerals (d ∷ es) = Digit.numeral d ∷ numerals es
  exact-cut : observe (run 1 4 4 bound) ≡ 4 ∷ []
  exact-cut = refl
