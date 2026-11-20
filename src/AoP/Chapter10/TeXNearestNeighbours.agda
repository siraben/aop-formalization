{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXNearestNeighbours where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; rid; sum-mono; chain; compare)
open import AoP.Chapter02.Polynomial using (inl; inr; _⊎_)
open import AoP.Chapter04.FractionCrossOrder using (module Arithmetic)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _-_; _*_)

-- At a fixed decimal width the common denominator cancels. Bracket
-- the target numerator between two successive grid points. Every rival
-- is on one of the two outer half-lines, so one comparison suffices.
err : Nat → Nat → Nat
err x y = (x - y) + (y - x)
private
  vanish : ∀ {x y} → x ≤ y → x - y ≡ 0
  vanish {0} {0} _ = refl
  vanish {0} {suc y} _ = refl
  vanish (s≤ p) = vanish p
  anti-sub : ∀ t {x y} → x ≤ y → t - y ≤ t - x
  anti-sub 0 {0} {0} p = z≤
  anti-sub 0 {0} {suc y} p = z≤
  anti-sub 0 {suc x} {suc y} p = z≤
  anti-sub (suc t) {0} {0} p = rid _
  anti-sub (suc t) {0} {suc y} p = chain (anti-sub t {0} {y} z≤) (AoP.Common.NatOrder.weaken (rid t))
  anti-sub (suc t) (s≤ p) = anti-sub t p
  mono-sub : ∀ t {x y} → x ≤ y → x - t ≤ y - t
  mono-sub 0 p = p
  mono-sub (suc t) z≤ = z≤
  mono-sub (suc t) (s≤ p) = mono-sub t p
  split : ∀ a b → (a ≤ b) ⊎ (suc b ≤ a)
  split 0 b = inl z≤
  split (suc a) 0 = inr (s≤ z≤)
  split (suc a) (suc b) with split a b
  ... | inl p = inl (s≤ p)
  ... | inr p = inr (s≤ p)

left : ∀ x y t → x ≤ y → y ≤ t → err y t ≤ err x t
left x y t xy yt rewrite vanish yt | vanish (chain xy yt) = anti-sub t xy
right : ∀ t x y → t ≤ x → x ≤ y → err x t ≤ err y t
right t x y tx xy rewrite vanish tx | vanish (chain tx xy) = sum-mono (mono-sub t xy) z≤

module Choose (w t a : Nat) (lo : a * w ≤ t) (hi : t ≤ suc a * w) where
  cost = λ i → err (i * w) t
  winner : Σ Nat (λ i → ∀ j → cost i ≤ cost j)
  winner with compare (cost a) (cost (suc a))
  ... | inl le = a , λ j → cases j (split j a)
    where cases : ∀ j → (j ≤ a) ⊎ (suc a ≤ j) → cost a ≤ cost j
          cases j (inl p) = left _ _ t (Arithmetic.scale w p) lo
          cases j (inr p) = chain le (right t _ _ hi (Arithmetic.scale w p))
  ... | inr ge = suc a , λ j → cases j (split j a)
    where cases : ∀ j → (j ≤ a) ⊎ (suc a ≤ j) → cost (suc a) ≤ cost j
          cases j (inl p) = chain ge (left _ _ t (Arithmetic.scale w p) lo)
          cases j (inr p) = right t _ _ hi (Arithmetic.scale w p)
