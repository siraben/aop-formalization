{-# OPTIONS --safe --without-K #-}
module AoP.ListFoldByMembership where

open import AoP.Prelude
open import AoP.Relations using (_←_; Fold; nil; cons)
open import AoP.Power using (ℙ; _≐_)

-- §5.5 (5.12), specialized to cons-lists. The accumulator of the
-- ordinary fold is the predicate of all possible answers. The cons
-- algebra first reads a tail answer by membership, then runs the
-- relational step. Its existential witness records the chosen answer.
module Calculate {A B : Set} (base : ℙ B) (step : B ← (A × B)) where
  extend : A → ℙ B → ℙ B
  extend a tail b = Σ B λ t → tail t × step b (a , t)
  answers : List A → ℙ B
  answers [] = base
  answers (a ∷ xs) = extend a (answers xs)

  sound : ∀ {xs b} → answers xs b → Fold base step b xs
  sound {[]} p = nil p
  sound {a ∷ xs} (t , tail , edge) = cons edge (sound tail)
  complete : ∀ {xs b} → Fold base step b xs → answers xs b
  complete (nil p) = p
  complete (cons e tail) = _ , complete tail , e

  -- The relational algebra equation splits into a nil and a cons
  -- equation for fibres. Every solution has exactly the answers of
  -- the ordinary fold, by induction and transport of the tail witness.
  module Rival (X : B ← List A) (empty : (λ b → X b []) ≐ base)
    (push : ∀ a xs → (λ b → X b (a ∷ xs)) ≐ extend a (λ t → X t xs)) where
    only : ∀ xs → (λ b → X b xs) ≐ answers xs
    only [] = empty
    fst (only (a ∷ xs)) b p with fst (push a xs) b p
    ... | t , tail , e = t , fst (only xs) t tail , e
    snd (only (a ∷ xs)) b (t , tail , e) = snd (push a xs) b (t , snd (only xs) t tail , e)
