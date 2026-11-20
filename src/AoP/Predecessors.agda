{-# OPTIONS --safe --without-K #-}
module AoP.Predecessors where

open import AoP.Prelude
open import AoP.Naturals using (foldn)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- Exercise 3.6. Return the positive numbers up to the input in descending
-- order. A successor step must put the new index in front. A plain step
-- sees only its previous result, so carry that index alongside the list,
-- as in the auxiliary-fold derivation of exercise 3.4.
preds : Nat → List Nat
preds zero = []
preds (suc n) = suc n ∷ preds n

step : List Nat × Nat → List Nat × Nat
step (xs , n) = (suc n ∷ xs) , suc n

state : Nat → List Nat × Nat
state = foldn ([] , 0) step

invariant : ∀ n → state n ≡ (preds n , n)
invariant zero = refl
invariant (suc n) = begin
  state (suc n) ≡⟨⟩
  step (state n) ≡⟨ cong step (invariant n) ⟩
  (suc n ∷ preds n , suc n) ∎

correct : ∀ n → fst (state n) ≡ preds n
correct n = cong fst (invariant n)

example : fst (state 4) ≡ 4 ∷ 3 ∷ 2 ∷ 1 ∷ []
example = refl
