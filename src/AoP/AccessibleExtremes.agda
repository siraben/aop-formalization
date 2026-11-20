{-# OPTIONS --safe --without-K #-}
module AoP.AccessibleExtremes where

open import AoP.Prelude
open import AoP.Relations using (_←_)
open import AoP.Inductive using (Acc; acc)
open import AoP.Complement using (⊥)

-- Exercise 6.14. The empty predecessor relation has no recursive
-- calls, so its accessibility proof ends immediately at every point.
empty : ∀ {A : Set} (x : A) → Acc (λ _ _ → ⊥) x
empty x = acc λ _ ()

-- A single self-edge already rules out accessibility at its vertex.
-- Descend into the smaller accessibility proof at that same vertex.
loop : ∀ {A} {R : A ← A} {x} → R x x → Acc R x → ⊥
loop edge (acc smaller) = loop edge (smaller _ edge)

identity : ∀ {A : Set} (x : A) → Acc _≡_ x → ⊥
identity x = loop refl

universal : ∀ {A : Set} (x : A) → Acc (λ _ _ → ⊤) x → ⊥
universal x = loop tt

-- On an empty carrier even the universal relation is well-founded.
vacuous : (R : ⊥ ← ⊥) → ∀ x → Acc R x
vacuous R ()
