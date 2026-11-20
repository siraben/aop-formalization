{-# OPTIONS --safe --without-K #-}
module AoP.UniqueMinimum where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Thinning using (Min)
open import AoP.TwoMinima using (module Law)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Bool using (Bool; false; true)

module Criterion {A : Set} (R : A ← A) where
  Unique = ∀ (X : A → Set) a b → Min R a X → Min R b X → a ≡ b
  Anti = ∀ a b → R a b → R b a → a ≡ b

  unique : Anti → Unique
  unique anti X a b (ax , lower) (bx , lower′) = anti a b (lower b bx) (lower′ a ax)

  antisymmetric : (∀ a → R a a) → Unique → Anti
  antisymmetric rr simple a b ab ba with Law.witness R R rr rr (ab , ba)
  ... | X , ma , mb = simple X a b ma mb

-- Without reflexivity a two-cycle can have no minima at all: either
-- candidate would have to precede itself, since it belongs to the set.
data Cycle : Bool ← Bool where
  up : Cycle true false
  down : Cycle false true

no-loop : ∀ a → Cycle a a → ⊥
no-loop true ()
no-loop false ()

vacuously-unique : Criterion.Unique Cycle
vacuously-unique X a b (ax , lower) mb with no-loop a (lower a ax)
... | ()

fails-anti : Criterion.Anti Cycle → ⊥
fails-anti anti with anti true false up down
... | ()
