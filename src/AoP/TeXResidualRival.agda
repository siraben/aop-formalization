{-# OPTIONS --safe --without-K #-}
module AoP.TeXResidualRival where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; s≤; z≤; chain; rid; sum-mono)
open import AoP.TeXGridStop using (InCell)
open import AoP.OpenUpperDigit using (Upper)
open import AoP.FractionCrossOrder using (module Arithmetic)
open Arithmetic using (assoc; dist; sym; switch)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _-_; _*_)

-- To compare a rival numerator t against the greedy digit d, drop
-- d*v from t, saturating at zero. The lower endpoint is clipped in
-- exactly the same way. This does not assume the rival starts with d.
private
  mono-sub : ∀ a {x y} → x ≤ y → x - a ≤ y - a
  mono-sub 0 h = h
  mono-sub (suc a) z≤ = z≤
  mono-sub (suc a) (s≤ h) = mono-sub a h
  cancel : ∀ a b c → (a + b) - (a + c) ≡ b - c
  cancel 0 b c = refl
  cancel (suc a) b c = cancel a b c
  sub-scale : ∀ a b v → (a - b) * v ≡ a * v - b * v
  sub-scale a 0 v = refl
  sub-scale 0 (suc b) v with v
  ... | 0 = zero-sub (b * 0)
    where zero-sub : ∀ u → 0 ≡ 0 - u
          zero-sub 0 = refl
          zero-sub (suc u) = refl
  ... | suc v = refl
  sub-scale (suc a) (suc b) v = sub-scale a b v ∙ sym (cancel v (a * v) (b * v))

  positive : ∀ a y → suc a ≤ y → 1 ≤ y - a
  positive 0 y h = h
  positive (suc a) (suc y) (s≤ h) = positive a y h
  strict-sub : ∀ a x y → suc a ≤ y → suc x ≤ y → suc (x - a) ≤ y - a
  strict-sub 0 x y pos h = h
  strict-sub (suc a) 0 (suc y) (s≤ pos) h = positive a y pos
  strict-sub (suc a) (suc x) (suc y) (s≤ pos) (s≤ h) = strict-sub a x y pos h

upper : ∀ w q d v t → suc ((d * w) * v) ≤ q * v → suc (t * w) ≤ q * v → suc ((t - d * v) * w) ≤ (q - d * w) * v
upper w q d v t pos h rewrite sub-scale t (d * v) w | sub-scale q (d * w) v | switch d v w = strict-sub (d * w * v) (t * w) (q * v) pos h

lower : ∀ w p d v t → p * v ≤ t * w → (p - d * w) * v ≤ (t - d * v) * w
lower w p d v t h rewrite sub-scale p (d * w) v | sub-scale t (d * v) w | switch d v w = mono-sub (d * w * v) h

-- One fewer decimal place suffices for the residual problem, using an
-- arbitrary rival t at the old width. A positive v preserves the strict
-- upper gap even when the projected rival numerator clips to zero.
drop : ∀ w p q d v t → Upper w q d → InCell w (p * suc v) (q * suc v) t → InCell w ((p - d * w) * suc v) ((q - d * w) * suc v) (t - d * suc v)
drop w p q d v t (gap , _) (lo , hi) = lower w p d (suc v) t lo , upper w q d (suc v) t strict hi
  where pad : ∀ a b → b ≤ a + b
        pad 0 b = rid b
        pad (suc a) b = AoP.NatOrder.weaken (pad a b)
        strict : suc (d * w * suc v) ≤ q * suc v
        strict = chain (s≤ (pad v _)) (Arithmetic.scale (suc v) gap)
