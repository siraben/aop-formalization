{-# OPTIONS --safe --without-K #-}
module AoP.TransposeCounterexample where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Shunting using (Id)
open import AoP.Power using (ℙ; Λ; _≐_)
open import AoP.Complement using (⊥)

-- Exercise 4.44. Precompose identity on the singleton by the empty
-- relation. Transposing the composite returns an empty subset at tt.
-- In contrast, composing *after* transposition needs an intermediate
-- element supplied by the empty relation; it returns no subset at all.
empty : ⊤ ← ⊤
empty _ _ = ⊥

Left Right : ℙ ⊤ → Set
Left X = Λ (Id ∘ empty) tt ≐ X
Right X = Σ ⊤ λ u → (Λ Id u ≐ X) × empty u tt

nothing : ℙ ⊤
nothing _ = ⊥

returns-empty : Left nothing
returns-empty = (λ { _ (_ , _ , p) → p }) , (λ { _ () })

no-output : ∀ X → Right X → ⊥
no-output X (_ , _ , p) = p

fails : (∀ X → Left X → Right X) → ⊥
fails incl = no-output nothing (incl nothing returns-empty)
