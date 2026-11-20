{-# OPTIONS --safe --without-K #-}
module AoP.LowerMinimum where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Thinning using (Min)

-- Exercises 7.5 and 7.12. A predecessor of a lower bound is still
-- a lower bound. Reflexivity supplies a witness in the other direction.
-- Restrict to members and the same calculation characterizes minima.
module Law {A : Set} (R : A ← A) (rr : ∀ a → R a a)
           (trans : ∀ {a b c} → R a b → R b c → R a c) where
  Lower : A → (A → Set) → Set
  Lower a X = ∀ b → X b → R a b

  lower : ∀ {a X} → (Σ A λ b → R a b × Lower b X) → Lower a X
  lower (_ , ab , bound) c xc = trans ab (bound c xc)

  factor : ∀ {a X} → Lower a X → Σ A λ b → R a b × Lower b X
  factor {a} bound = a , rr a , bound

  -- Membership of a is indispensable: a predecessor of a minimum
  -- can lie outside X. The intermediate b carries the lower-bound proof.
  minimum : ∀ {a X} → X a × (Σ A λ b → R a b × Min R b X) → Min R a X
  minimum (xa , b , ab , _ , bound) = xa , lower (b , ab , bound)

  witness : ∀ {a X} → Min R a X → X a × (Σ A λ b → R a b × Min R b X)
  witness {a} m = fst m , a , rr a , m
