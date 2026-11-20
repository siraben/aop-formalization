{-# OPTIONS --safe --without-K #-}
module AoP.LexCounterexample where

open import AoP.Prelude
open import AoP.Polynomial using (inl; inr)
open import AoP.LexSubsequence using (module Law)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)

data Below : Bool → Bool → Set where rise : Below false true
module L = Law Below (λ { rise () }) (λ where
  false false → inr (inl refl)
  false true → inl rise
  true false → inr (inr rise)
  true true → inr (inl refl))

-- Exercise 7.42. Outside the descending invariant, equality of
-- heads does not justify keeping the new one. Use 0 < 1. Comparing
-- 001 with 01 skips their common 0, then encounters 0 < 1.
tail = false ∷ true ∷ []
kept = false ∷ tail

keep-below-drop : L.Lex kept tail
keep-below-drop = L.common (L.less rise)

not-a-maximum : L.Lex tail kept → ⊥
not-a-maximum (L.less ())
not-a-maximum (L.common (L.less ()))
