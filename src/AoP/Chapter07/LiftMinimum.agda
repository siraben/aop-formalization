{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.LiftMinimum where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Relations
open import AoP.Chapter07.LiftBound using (module Bound)
open import AoP.Chapter05.PowerRelator using (Lift; cover)
open import AoP.Chapter08.Thinning using (Min)

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
