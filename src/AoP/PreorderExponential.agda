{-# OPTIONS --safe --without-K #-}
module AoP.PreorderExponential where

open import AoP.Prelude

-- Exercise 3.35. Write x ≼ y when there is an arrow x → y. Finite
-- products then mean a greatest object and binary meets. For each a,b
-- the exponential b^a must be a greatest x satisfying x ∧ a ≼ b.
-- Greatest means up to mutual reachability; antisymmetry is unnecessary.
module Closed {P : Set} (_≼_ : P → P → Set) (id : ∀ x → x ≼ x)
              (then≤ : ∀ {x y z} → x ≼ y → y ≼ z → x ≼ z)
              (_∧_ : P → P → P) (left : ∀ x a → (x ∧ a) ≼ x)
              (right : ∀ x a → (x ∧ a) ≼ a)
              (pair : ∀ {t x a} → t ≼ x → t ≼ a → t ≼ (x ∧ a)) where
  module At (a b e : P) where
    Greatest = ((e ∧ a) ≼ b) × (∀ x → (x ∧ a) ≼ b → x ≼ e)
    Adjunction = ∀ x → ((x ≼ e → (x ∧ a) ≼ b) × ((x ∧ a) ≼ b → x ≼ e))

    -- Evaluation is the uncurrying of the identity on e.
    greatest : Adjunction → Greatest
    greatest adj = fst (adj e) (id e) , (λ x → snd (adj x))

    -- To uncurry an arrow x → e, pair it (after projection) with the
    -- argument a and then evaluate. Currying is exactly maximality.
    adjunction : Greatest → Adjunction
    adjunction (eval , curry) x = (λ p → then≤ (pair (then≤ (left x a) p) (right x a)) eval) , curry x
