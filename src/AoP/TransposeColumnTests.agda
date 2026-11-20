{-# OPTIONS --safe --without-K #-}
module AoP.TransposeColumnTests where

open import AoP.Prelude
open import AoP.Power using (ℙ; Λ; _≐_)
open import AoP.Relations using (_←_)
open import Agda.Primitive using (Level)

-- §4.6. Permit large input objects: the membership column is indexed by
-- subsets of A, which live one universe above A. Each observed edge is
-- still small. Division compares columns by containment of their outputs.
under : ∀ {i j : Level} {A : Set} {B : Set i} {C : Set j} →
  (A → B → Set) → (A → C → Set) → B → C → Set
under R S b c = ∀ a → R a b → S a c

module Law {A B : Set} (R : A ← B) where
  member : A → ℙ A → Set
  member a X = X a
  tests : ℙ A → B → Set
  tests X b = under member R X b × under R member b X
  -- A candidate subset X can omit no output and include no extra one.
  -- The first division rules out extras; the second rules out omissions.
  accepted : ∀ X b → tests X b → Λ R b ≐ X
  accepted X b (no-extra , no-missing) = no-missing , no-extra
  required : ∀ X b → Λ R b ≐ X → tests X b
  required X b (into , from) = from , into

  -- Reflect at membership itself. The transpose graph is now identity
  -- on predicates up to extensional equality, giving subset antisymmetry.
module Subsets (A : Set) where
  member : A → ℙ A → Set
  member a X = X a
  subset = under member member
  antisymmetric : ∀ X Y → subset X Y → subset Y X → X ≐ Y
  antisymmetric X Y p q = p , q
