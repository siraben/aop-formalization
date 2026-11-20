{-# OPTIONS --safe --without-K #-}
module AoP.AccessibleNoDescent where

open import AoP.Prelude
open import AoP.Inductive using (Acc; acc)
open import AoP.Relations using (_←_; _⊆_; _∘_)
open import AoP.Complement using (⊥)

-- §6.5. A relation X that can always take another predecessor step
-- has no edges when all inputs are accessible. Fixing the output b
-- keeps the induction on the input independent of the output type.
module Law {A : Set} (R : A ← A) where
  WellFounded : Set₁
  WellFounded = ∀ {B : Set} (X : B ← A) → X ⊆ X ∘ R → ∀ {b a} → X b a → ⊥

  forward : (∀ a → Acc R a) → WellFounded
  forward all X again {b} {a} = descend (all a)
    where
      descend : ∀ {x} → Acc R x → X b x → ⊥
      descend (acc smaller) edge with again edge
      ... | y , next , step = descend (smaller y step) next

  -- Conversely, classically an inaccessible vertex has an inaccessible
  -- predecessor. If there were none, double-negation elimination at
  -- each child would build the parent's accessibility certificate.
  module Classical (dne : (P : Set) → ((P → ⊥) → ⊥) → P) where
    bad : ⊤ ← A
    bad _ x = Acc R x → ⊥
    again : bad ⊆ bad ∘ R
    again {tt} {x} no = dne _ λ absent → no (acc λ y step → dne _ λ child-bad → absent (y , child-bad , step))
    backward : WellFounded → ∀ a → Acc R a
    backward wf a = dne _ (λ bad-a → wf bad again {tt} {a} bad-a)
