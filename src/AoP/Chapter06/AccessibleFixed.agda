{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.AccessibleFixed where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_)
open import AoP.Chapter06.Inductive using (Acc; acc)

-- Exercise 6.12 for concrete predicates. A state belongs to Box X
-- precisely when all its predecessors belong to X. Accessibility and
-- the full predicate are both fixed points, which gives the converse.
module Law {A : Set} (R : A ← A) where
  Pred = A → Set
  Box : Pred → Pred
  Box X a = ∀ b → R b a → X b

  record Fixed (X : Pred) : Set where
    field close : ∀ a → Box X a → X a
          open-up : ∀ a → X a → Box X a

  least : ∀ X → Fixed X → ∀ a → Acc R a → X a
  least X fx a (acc down) = Fixed.close fx a λ b edge → least X fx b (down b edge)

  Unique : Set₁
  Unique = ∀ X Y → Fixed X → Fixed Y → ∀ a → (X a → Y a) × (Y a → X a)

  forward : (∀ a → Acc R a) → Unique
  forward wf X Y fx fy a = (λ _ → least Y fy a (wf a)) , (λ _ → least X fx a (wf a))

  accessible : Fixed (Acc R)
  Fixed.close accessible a = acc
  Fixed.open-up accessible a (acc down) = down

  full : Fixed (λ _ → ⊤)
  Fixed.close full _ _ = tt
  Fixed.open-up full _ _ _ _ = tt

  backward : Unique → ∀ a → Acc R a
  backward unique a = fst (unique (λ _ → ⊤) (Acc R) full accessible a) tt
