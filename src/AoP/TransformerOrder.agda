{-# OPTIONS --safe --without-K #-}
module AoP.TransformerOrder where

open import AoP.Prelude
open import AoP.Power using (ℙ)
open import AoP.PreorderFibres using (Incl)

-- Exercise 4.51. Compare predicate transformers on every input set
-- and every candidate output member. A monotone transformer preserves
-- this order under postcomposition. Conversely, constant transformers
-- isolate any desired inclusion of two sets, regardless of the input set.
module Law {A B : Set} (h : ℙ B → ℙ A) where
  Monotone = ∀ X Y → Incl X Y → Incl (h X) (h Y)

  Below : ∀ {C D : Set} → (ℙ C → ℙ D) → (ℙ C → ℙ D) → Set₁
  Below f g = ∀ X → Incl (f X) (g X)

  Preserves = ∀ {C : Set} (f g : ℙ C → ℙ B) → Below f g →
              Below (λ X → h (f X)) (λ X → h (g X))

  postcompose : Monotone → Preserves
  postcompose mono f g le X = mono (f X) (g X) (le X)

  test : Preserves → Monotone
  test preserves X Y le = preserves {⊤} (λ _ → X) (λ _ → Y) (λ _ → le) (λ _ → ⊤)
