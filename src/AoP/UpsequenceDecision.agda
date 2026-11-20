{-# OPTIONS --safe --without-K #-}
module AoP.UpsequenceDecision where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; chain; rid; s≤)
open import AoP.ConversionCost using (len)
open import AoP.UpsequenceDominance using (module Law)
open import AoP.ParagraphMinimum using (Dec; le?)
open import AoP.Polynomial using (inl; inr)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat; suc)
open Law _≤_

-- Exercise 8.29. Decide the quantified acceptance comparison by its
-- tightest test: for a nonempty competitor, try its own head. An
-- empty competitor accepts everything, including a value exceeding
-- the head of any nonempty replacement.
Covers : List Nat → List Nat → Set
Covers xs ys = ∀ a → Accept a ys → Accept a xs
private
  impossible : ∀ n → suc n ≤ n → ⊥
  impossible 0 ()
  impossible (suc n) (s≤ p) = impossible n p

covers? : ∀ xs ys → Dec (Covers xs ys)
covers? [] ys = inl (λ _ _ → tt)
covers? (x ∷ xs) [] = inr (λ f → impossible x (f (suc x) tt))
covers? (x ∷ xs) (y ∷ ys) with le? y x
... | inl p = inl (λ a q → chain q p)
... | inr no = inr (λ f → no (f y (rid y)))

dominates? : ∀ xs ys → Dec (Dominates xs ys)
dominates? xs ys with le? (len ys) (len xs) | covers? xs ys
... | inr no | _ = inr (λ p → no (fst p))
... | inl _ | inr no = inr (λ p → no (snd p))
... | inl le | inl f = inl (le , f)
