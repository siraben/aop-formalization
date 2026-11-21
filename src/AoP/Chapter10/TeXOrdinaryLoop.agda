{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXOrdinaryLoop where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_)
open import AoP.Chapter10.TeXUpperPrefix using (W; module Prefix)
open import AoP.Chapter10.TeXUpperGridParity using (Grid; g1; g2; g3; g4; g5)
open import AoP.Chapter10.TeXPrinterStep using (module Emit)
open import AoP.Chapter10.TeXResidualLoop using (module Loop; next-bound; pred; nonzero; Result; exhausted; printed; prepend)
open import AoP.Chapter03.TeXFraction using (Digit)
open import AoP.Chapter03.Horner using (map)
open import AoP.Chapter10.StrictUpperQuotient using (choose)
open import AoP.Chapter04.FractionCrossOrder using (module Arithmetic)
open import Agda.Builtin.Nat using (Nat; suc; _*_; _+_; _-_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)

-- Execute the uncorrected quotient directly. Compare *all* emitted
-- numerals and preserve observable exhaustion, not just decoded values.
cons : Nat → Maybe (List Nat) → Maybe (List Nat)
cons d nothing = nothing
cons d (just ds) = just (d ∷ ds)
ordinary : Nat → Nat → Nat → Maybe (List Nat)
ordinary fuel 0 q = just []
ordinary 0 (suc p) q = nothing
ordinary (suc fuel) (suc p) q = cons d (ordinary fuel (suc p * 10 - d * W) (q * 10 - d * W))
  where d = choose 131071 (q * 10)
observe : Result → Maybe (List Nat)
observe exhausted = nothing
observe (printed ds) = just (map Digit.numeral ds)
cons-law : ∀ d r → observe (prepend d r) ≡ cons (Digit.numeral d) (observe r)
cons-law d exhausted = refl
cons-law d (printed ds) = refl

data Grids : Nat → Nat → Set where
  done : ∀ {D} → Grids D 0
  more : ∀ {D f} → Grid (D * 10) → Grids (D * 10) f → Grids D (suc f)
five : Grids 1 5
five = more g1 (more g2 (more g3 (more g4 (more g5 done))))

module Agreement (n : Nat) where
  open Prefix n
  same : ∀ {D z} fuel p j (b : suc j ≤ W) → Run D z (suc j) → Grids D fuel →
    observe (Loop.run 131071 fuel p j b) ≡ ordinary fuel p (suc j)
  same f 0 j b run grids = refl
  same 0 (suc p) j b run grids = refl
  same (suc f) (suc p) j b run (more grid rest) = begin
    observe (prepend E.letter tail) ≡⟨ cons-law E.letter tail ⟩
    cons E.d (observe tail) ≡⟨ cong (cons E.d) (same f E.low (pred E.high) bound next rest) ⟩
    cons E.d (ordinary f E.low (suc (pred E.high))) ≡⟨ cong (λ q → cons E.d (ordinary f E.low q)) (Arithmetic.sym pos) ⟩
    cons E.d (ordinary f E.low E.high) ≡⟨ cong (λ d → cons d (ordinary f (suc p * 10 - d * W) (suc j * 10 - d * W))) digit ⟩
    ordinary (suc f) (suc p) (suc j) ∎
    where module E = Emit 131071 j 0 (suc p) b
          bound = next-bound 131071 E.high E.next-high
          tail = Loop.run 131071 f E.low (pred E.high) bound
          pos = nonzero E.high (fst E.next-high)
          digit = same-digit grid run (9 + j * 10) refl
          next : Run _ _ (suc (pred E.high))
          next = subst-run pos (emit E.d E.high run E.exact) -- zero prefix exposes the local divmod equation
            where subst-run : ∀ {D z a b} → a ≡ b → Run D z a → Run D z b
                  subst-run refl h = h

  -- The actual initial upper endpoint is 2n+1. The lower endpoint
  -- may be supplied independently: zero succeeds before consuming fuel.
  from-start : ∀ p (b : hi ≤ W) →
    observe (Loop.run 131071 5 p (n * 2) b) ≡ ordinary 5 p hi
  from-start p b = same 5 p (n * 2) b start five
