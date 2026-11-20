{-# OPTIONS --safe --without-K #-}
module AoP.TeXUpperResidual where

open import AoP.Prelude
open import AoP.OpenUpperDigit using (Upper)
open import AoP.NatOrder using (_≤_; z≤; s≤; chain)
open import AoP.FractionCrossOrder using (module Arithmetic)
open Arithmetic using (dist; switch; assoc; sym; swap)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _-_; _*_)

-- A strict digit leaves a positive residual, including when the upper
-- endpoint is exactly on the grid (then the residual is one whole w).
private
  weaken : ∀ {a b} → suc a ≤ b → a ≤ b
  weaken {0} p = z≤
  weaken {suc a} (s≤ p) = s≤ (weaken p)
  restore : ∀ a b → a ≤ b → a + (b - a) ≡ b
  restore 0 b p = refl
  restore (suc a) (suc b) (s≤ p) = cong suc (restore a b p)
  positive : ∀ a b → suc a ≤ b → 1 ≤ b - a
  positive 0 b p = p
  positive (suc a) (suc b) (s≤ p) = positive a b p
  bounded : ∀ a b w → b ≤ a + w → b - a ≤ w
  bounded 0 b w p = p
  bounded (suc a) 0 w p = z≤
  bounded (suc a) (suc b) w (s≤ p) = bounded a b w p

module Step (w z q d : Nat) (local : Upper w (q * 10) d) where
  residual = q * 10 - d * w
  positive-bound : 1 ≤ residual
  positive-bound = positive (d * w) (q * 10) (fst local)
  upper-bound : residual ≤ w
  upper-bound = bounded (d * w) (q * 10) w (cast (snd local))
    where cast : q * 10 ≤ w + d * w → q * 10 ≤ d * w + w
          cast p = subst (comm w (d * w)) p
            where comm : ∀ a b → a + b ≡ b + a
                  comm 0 b = sym (Arithmetic.unit b)
                  comm (suc a) b = cong suc (comm a b) ∙ sym (Arithmetic.move b a)
                  subst : ∀ {a b} → a ≡ b → q * 10 ≤ a → q * 10 ≤ b
                  subst refl h = h
  reconstruct : (z * 10 + d) * w + residual ≡ (z * w + q) * 10
  reconstruct = begin
    (z * 10 + d) * w + residual ≡⟨ cong (_+ residual) (dist (z * 10) d w) ⟩
    (z * 10 * w + d * w) + residual ≡⟨ assoc (z * 10 * w) (d * w) residual ⟩
    z * 10 * w + (d * w + residual) ≡⟨ cong (z * 10 * w +_) (restore (d * w) (q * 10) (weaken (fst local))) ⟩
    z * 10 * w + q * 10 ≡⟨ cong (_+ (q * 10)) (switch z 10 w) ⟩
    z * w * 10 + q * 10 ≡⟨ sym (dist (z * w) q 10) ⟩
    (z * w + q) * 10 ∎
