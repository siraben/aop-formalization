{-# OPTIONS --safe --without-K #-}
module AoP.RelDistribution where

open import AoP.Prelude
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Relations
open import AoP.Shunting using (graph; Id)
open import AoP.Complement using (⊥)

-- Exercise 3.24. In Rel, disjoint union serves as both coproduct and
-- categorical product: a relation to a tagged target amounts to one
-- relation for each tag. Thus the comparison from (A × B)+(A × C)
-- to A × (B+C) must merge the two copies of A. Take A to be a singleton
-- and B and C empty. Even an arbitrary *relation* cannot undo that merge.
Source = (⊤ ⊎ ⊥) ⊎ (⊤ ⊎ ⊥)
Target = ⊤ ⊎ (⊥ ⊎ ⊥)
merge : Source → Target
merge (inl (inl x)) = inl x
merge (inr (inl x)) = inl x
merge (inl (inr ()))
merge (inr (inr ()))

left right : Source
left = inl (inl tt)
right = inr (inl tt)

-- If U recovers left, it also relates the same intermediate value to
-- left when started at right. The composite then relates distinct tags.
no-inverse : (U : Source ← Target) → Id ⊆ U ∘ graph merge → U ∘ graph merge ⊆ Id → ⊥
no-inverse U total sound with total {left} {left} refl
... | y , u , eq = distinct (sound {left} {right} (y , u , eq))
  where distinct : left ≡ right → ⊥
        distinct ()
