{-# OPTIONS --safe --without-K #-}
module AoP.TeXResidualAccept where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; z≤; s≤; rid; sum-mono; chain)
open import AoP.TeXGridStop using (InCell)
open import AoP.FractionCrossOrder using (module Arithmetic)
open Arithmetic using (dist; sym; switch; move; comm)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_; _-_)

-- A successful suffix with numerator x and scale v lies in the
-- updated interval. Restore the consumed digit's contribution to
-- both endpoints, accounting for clipping at zero on the lower side.
private
  cover : ∀ a b → b ≤ a + (b - a)
  cover 0 b = rid b
  cover (suc a) 0 = z≤
  cover (suc a) (suc b) = s≤ (cover a b)
  times : ∀ a b c → (a * b) * c ≡ a * (b * c)
  times 0 b c = refl
  times (suc a) b c rewrite dist b (a * b) c | times a b c = refl

accept : ∀ w p q d v x → d * w + (q * 10 - d * w) ≡ q * 10 →
  InCell w ((p * 10 - d * w) * v) ((q * 10 - d * w) * v) x →
  InCell w (p * (10 * v)) (q * (10 * v)) (d * v + x)
accept w p q d v x restores (lo , hi) rewrite sym (times p 10 v) | sym (times q 10 v) | dist (d * v) x w | switch d v w | sym (move (d * w * v) (x * w)) =
  chain (Arithmetic.scale v (cover (d * w) (p * 10))) (lower (p * 10 - d * w) lo) , upper (q * 10 - d * w) restores hi
  where
  lower : ∀ r → r * v ≤ x * w → (d * w + r) * v ≤ d * w * v + x * w
  lower r h rewrite dist (d * w) r v = sum-mono (rid _) h
  upper : ∀ r → d * w + r ≡ q * 10 → suc (x * w) ≤ r * v → d * w * v + suc (x * w) ≤ q * 10 * v
  upper r eq h = cast (sym (dist (d * w) r v) ∙ cong (_* v) eq) (sum-mono (rid _) h)
    where cast : ∀ {a b c} → b ≡ c → a ≤ b → a ≤ c
          cast refl h = h
