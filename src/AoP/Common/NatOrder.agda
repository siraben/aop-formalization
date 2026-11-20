{-# OPTIONS --safe --without-K #-}
module AoP.Common.NatOrder where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)

-- Concrete order used for integral costs, weights, and scores. Unlike a
-- Boolean test, compare returns evidence usable directly in an optimality
-- calculation. In particular, adding nonnegative scores is monotone.
infix 4 _≤_
data _≤_ : Nat → Nat → Set where
  z≤ : ∀ {n} → zero ≤ n
  s≤ : ∀ {n m} → n ≤ m → suc n ≤ suc m

rid : ∀ n → n ≤ n
rid zero = z≤
rid (suc n) = s≤ (rid n)
chain : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
chain z≤ q = z≤
chain (s≤ p) (s≤ q) = s≤ (chain p q)
weaken : ∀ {x y} → x ≤ y → x ≤ suc y
weaken z≤ = z≤
weaken (s≤ p) = s≤ (weaken p)

sum-mono : ∀ {a b c d} → a ≤ b → c ≤ d → (a + c) ≤ (b + d)
sum-mono {b = zero} z≤ q = q
sum-mono {b = suc b} z≤ q = weaken (sum-mono {b = b} z≤ q)
sum-mono (s≤ p) q = s≤ (sum-mono p q)

compare : ∀ x y → (x ≤ y) ⊎ (y ≤ x)
compare zero y = inl z≤
compare (suc x) zero = inr z≤
compare (suc x) (suc y) with compare x y
... | inl p = inl (s≤ p)
... | inr q = inr (s≤ q)
