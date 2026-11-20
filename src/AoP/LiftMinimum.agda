{-# OPTIONS --safe --without-K #-}
module AoP.LiftMinimum where

open import AoP.Prelude
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Relations
open import AoP.LiftBound using (module Bound)
open import AoP.PowerRelator using (Lift; cover)
open import AoP.Thinning using (Min)

-- Exercise 7.18. The lifted lower-bound witness may omit the proposed
-- minimum b. Add b to the intermediate set. Its incoming S edge
-- supplies backward coverage, and reflexivity preserves the bound.
module Law {A B : Set} (R : B ← B) (S : B ← A) (X : A → Set)
           (rr : ∀ b → R b b) where
  module L = Bound R S X
  realize : ∀ b → (Σ A λ a → S b a × X a) → L.Lifted b →
            Σ (B → Set) λ Z → Min R b Z × Lift S Z X
  realize b (a , edge , xa) (Y , bound , old) = Z , (inl refl , lower) , cover back forth
    where
    Z : B → Set
    Z c = (c ≡ b) ⊎ Y c
    lower : ∀ c → Z c → R b c
    lower _ (inl refl) = rr b
    lower c (inr y) = bound c y
    back : ∀ c → Z c → Σ A λ x → X x × S c x
    back _ (inl refl) = a , xa , edge
    back c (inr y) = Lift.backward old c y
    forth : ∀ x → X x → Σ B λ c → Z c × S c x
    forth x xx with Lift.forward old x xx
    ... | c , y , s = c , inr y , s
