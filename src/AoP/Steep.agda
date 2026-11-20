{-# OPTIONS --safe --without-K #-}
module AoP.Steep where

open import AoP.Prelude
open import AoP.Folds using (⦅_∣_⦆)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_; _<_)

-- Exercise 3.3. In a steep list each entry exceeds the sum of everything
-- after it. [7,4,2,1] fails at the first entry because 4+2+1 equals 7.
-- The direct test recomputes suffix sums. Cache the sum beside the test
-- result so that each cons performs one addition and one comparison.
sum : List Nat → Nat
sum = ⦅ 0 ∣ _+_ ⦆

_and_ : Bool → Bool → Bool
true and b = b
false and b = false

steep : List Nat → Bool
steep [] = true
steep (a ∷ xs) = (sum xs < a) and steep xs

step : Nat → Nat × Bool → Nat × Bool
step a (s , ok) = (a + s) , ((s < a) and ok)

scan : List Nat → Nat × Bool
scan = ⦅ (0 , true) ∣ step ⦆

invariant : ∀ xs → scan xs ≡ (sum xs , steep xs)
invariant [] = refl
invariant (a ∷ xs) = begin
  step a (scan xs) ≡⟨ cong (step a) (invariant xs) ⟩
  step a (sum xs , steep xs) ≡⟨⟩
  (sum (a ∷ xs) , steep (a ∷ xs)) ∎

fast : List Nat → Bool
fast xs = snd (scan xs)

correct : ∀ xs → fast xs ≡ steep xs
correct xs = cong snd (invariant xs)

strict-boundary : fast (7 ∷ 4 ∷ 2 ∷ 1 ∷ []) ≡ false
strict-boundary = refl
passes : fast (8 ∷ 4 ∷ 2 ∷ 1 ∷ []) ≡ true
passes = refl
