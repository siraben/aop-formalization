{-# OPTIONS --safe --without-K #-}
module AoP.TeXLowerResidual where

open import AoP.Prelude
open import AoP.FractionCrossOrder using (module Arithmetic)
open Arithmetic using (assoc; dist; switch; sym)
open import AoP.NatOrder using (_≤_; z≤; s≤)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _-_; _*_)

-- A running printer has positive lower residual p, so its old lower
-- endpoint is exactly z*w+p. Natural subtraction in the transition
-- clips the new residual to zero precisely when the new prefix fits.
private
  cancel : ∀ t a b → (t + a) - (t + b) ≡ a - b
  cancel 0 a b = refl
  cancel (suc t) a b = cancel t a b

residual : ∀ w z p d → ((z * w + p) * 10) - ((z * 10 + d) * w) ≡ p * 10 - d * w
residual w z p d rewrite dist (z * w) p 10 | switch z w 10 | dist (z * 10) d w = cancel (z * 10 * w) (p * 10) (d * w)

fits : ∀ L v → L - v ≡ 0 → L ≤ v
fits 0 v e = z≤
fits (suc L) 0 ()
fits (suc L) (suc v) e = s≤ (fits L v e)

-- When the loop continues, restore an exact lower endpoint for the
-- next iteration, as required by the precondition of residual above.
restore : ∀ L v r → L - v ≡ suc r → v + suc r ≡ L
restore 0 0 r ()
restore 0 (suc v) r ()
restore (suc L) 0 r eq = sym eq
restore (suc L) (suc v) r eq = cong suc (restore L v r eq)
