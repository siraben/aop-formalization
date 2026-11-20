{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.OrderProducts where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; rid; chain)
open import AoP.Common.Prelude

-- Exercise 2.25. A projection from p to a means a ≤ p. Thus the
-- product of two naturals is their least common upper bound; reversing
-- the arrows gives their greatest common lower bound as coproduct.
maximum minimum : Nat → Nat → Nat
maximum zero b = b
maximum (suc a) zero = suc a
maximum (suc a) (suc b) = suc (maximum a b)
minimum zero b = zero
minimum (suc a) zero = zero
minimum (suc a) (suc b) = suc (minimum a b)

projections : ∀ a b → (a ≤ maximum a b) × (b ≤ maximum a b)
projections zero b = z≤ , rid b
projections (suc a) zero = rid _ , z≤
projections (suc a) (suc b) with projections a b
... | l , r = s≤ l , s≤ r

pair : ∀ {a b x} → a ≤ x → b ≤ x → maximum a b ≤ x
pair z≤ r = r
pair (s≤ l) z≤ = s≤ l
pair (s≤ l) (s≤ r) = s≤ (pair l r)

injections : ∀ a b → (minimum a b ≤ a) × (minimum a b ≤ b)
injections zero b = z≤ , z≤
injections (suc a) zero = z≤ , z≤
injections (suc a) (suc b) with injections a b
... | l , r = s≤ l , s≤ r

copair : ∀ {a b x} → x ≤ a → x ≤ b → x ≤ minimum a b
copair z≤ z≤ = z≤
copair (s≤ l) (s≤ r) = s≤ (copair l r)

-- In a preorder category any two parallel mediators are equivalent.
-- The inequalities above therefore establish existence and uniqueness.
example : (maximum 3 5 ≡ 5) × (minimum 3 5 ≡ 3)
example = refl , refl
