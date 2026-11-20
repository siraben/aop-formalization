{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.StrictBoundCounterexample where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter06.Inductive using (Acc; acc)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Chapter07.WellBounded using (Bounded; connected)
open import Agda.Builtin.Bool using (Bool; true; false)

-- Exercise 7.26, testing the strict-part criterion. Equality on two
-- distinct points is a preorder. Its strict part has no predecessors,
-- but the set containing both points has no minimum. Thus well-founded
-- strict comparison alone cannot imply well-boundedness for preorders.
Equal : Bool ← Bool
Equal = _≡_

reflexive : ∀ b → Equal b b
reflexive b = refl
transitive : Equal ∘ Equal ⊆ Equal
transitive (_ , refl , refl) = refl

Strict : Bool ← Bool
Strict a b = Equal a b × (Equal b a → ⊥)

well-founded : ∀ b → Acc Strict b
well-founded b = acc λ { _ (refl , no) → absurd (no refl) }
  where absurd : ∀ {A : Set} → ⊥ → A
        absurd ()

not-bounded : Bounded Equal → ⊥
not-bounded wb with connected wb true false
... | inl ()
... | inr ()
