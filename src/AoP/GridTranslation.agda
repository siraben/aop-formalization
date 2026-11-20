{-# OPTIONS --safe --without-K #-}
module AoP.GridTranslation where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; z≤; s≤; rid; sum-mono)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- Exercise 3.17. Two states agree at width w when the same multiples
-- of w are lower bounds. A digit contributes an integral number of
-- blocks: translating both states by that many blocks preserves every
-- threshold. No subtraction or divisibility decision is required.
Below : Nat → Nat → Nat → Set
Below w x y = ∀ t → t * w ≤ x → t * w ≤ y

private
  cancel : ∀ w {a b} → w + a ≤ w + b → a ≤ b
  cancel 0 p = p
  cancel (suc w) (s≤ p) = cancel w p
  assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
  assoc 0 b c = refl
  assoc (suc a) b c = cong suc (assoc a b c)

translate : ∀ w k {x y} → Below w x y → Below w (k * w + x) (k * w + y)
translate w 0 h = h
translate w (suc k) h 0 p = z≤
translate w (suc k) {x} {y} h (suc t) p rewrite assoc w (k * w) x | assoc w (k * w) y =
  sum-mono (rid w) (translate w k h t (cancel w p))
