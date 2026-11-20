{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.ListSetify where

open import AoP.Common.Prelude
open import AoP.Chapter05.Subsequences using (_∈_; here; there; image; preimage; subs; Subseq; sound; complete)
open import AoP.Chapter04.Power using (ℙ; _≐_; Λ; ℰ)
open import AoP.Chapter04.Shunting using (graph)
open import AoP.Chapter04.SingletonTranspose using (unit)
open import AoP.Chapter05.TransposeCombinations using (cup)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter03.Horner using (map)
private variable A B : Set

-- Exercises 5.21–22. Forget the order and multiplicity of a list by
-- retaining its membership predicate. A cons contributes its head's
-- singleton and all members of its tail. Mapping before setification
-- amounts to direct image: a mapped occurrence has an original index.
setify : List A → ℙ A
setify xs x = x ∈ xs

empty : setify {A} [] ≐ (λ _ → ⊥)
empty = (λ { _ () }) , (λ { _ () })

wrap : (a : A) → setify (a ∷ []) ≐ unit a
wrap a = (λ { _ here → refl ; _ (there ()) }) , (λ { _ refl → here })

cons-law : (a : A) (xs : List A) → setify (a ∷ xs) ≐ cup (unit a , setify xs)
cons-law a xs = (λ { _ here → inl refl ; _ (there p) → inr p }) ,
                (λ { _ (inl refl) → here ; _ (inr p) → there p })

map-law : (f : A → B) (xs : List A) → setify (map f xs) ≐ ℰ (graph f) (setify xs)
map-law f xs = (λ y p → let x , occurs , eq = preimage f xs p in x , eq , occurs) ,
               (λ { _ (x , refl , occurs) → image f occurs })

subsequences : (xs : List A) → setify (subs xs) ≐ Λ Subseq xs
subsequences xs = (λ _ → sound xs) , (λ _ → complete)
