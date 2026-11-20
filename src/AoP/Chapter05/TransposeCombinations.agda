{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.TransposeCombinations where

open import AoP.Common.Prelude
open import AoP.Chapter02.ArrowCategory using () renaming (_×_ to _×′_)
open import AoP.Chapter02.Polynomial using (_⊎_)
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Power using (ℙ; Λ; _≐_)
open import AoP.Chapter04.Complement using (_⊔_)
open import AoP.Chapter05.RelationalProducts using (_⊗_)
private variable A B C D : Set

-- Exercise 5.20. Collect all possible outputs at a given input.
-- Alternatives give set union, simultaneous requirements intersection,
-- and independent inputs the cartesian product of their output sets.
cup cap : ℙ A ×′ ℙ A → ℙ A
cup (X , Y) a = X a ⊎ Y a
cap (X , Y) a = X a × Y a
cross : ℙ A ×′ ℙ B → ℙ (A × B)
cross (X , Y) (a , b) = X a × Y b

union : (R S : B ← A) (a : A) → Λ (R ⊔ S) a ≐ cup (Λ R a , Λ S a)
union R S a = (λ _ p → p) , (λ _ p → p)
intersection : (R S : B ← A) (a : A) → Λ (R ⊓ S) a ≐ cap (Λ R a , Λ S a)
intersection R S a = (λ _ p → p) , (λ _ p → p)
product : (R : B ← A) (S : D ← C) (a : A) (c : C) →
          Λ (R ⊗ S) (a , c) ≐ cross (Λ R a , Λ S c)
product R S a c = (λ { (_ , _) p → p }) , (λ { (_ , _) p → p })
