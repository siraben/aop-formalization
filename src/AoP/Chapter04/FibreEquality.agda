{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.FibreEquality where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Power using (Λ; ℙ; _≐_)
open import AoP.Chapter04.LeftDivision using (_＼_)

-- Exercise 4.48. The two power transposes have a common output when
-- the sets of possible results at their respective inputs coincide.
-- A witness on the graph-composition side is that intermediate set,
-- with extensional equality on each side. Division expresses each
-- direction of containment without mentioning the intermediate set.
module Law {A B C : Set} (R : C ← A) (S : C ← B) where
  Shared : A → B → Set₁
  Shared a b = Σ (ℙ C) λ X → (Λ R a ≐ X) × (Λ S b ≐ X)

  compares : A ← B
  compares = (R ＼ S) ⊓ ((S ＼ R) ˘)

  eliminate : ∀ a b → Shared a b → compares a b
  eliminate a b (X , (toR , fromR) , (toS , fromS)) =
    (λ {c} r → fromS c (toR c r)) , (λ {c} s → fromR c (toS c s))

  introduce : ∀ a b → compares a b → Shared a b
  introduce a b (forward , backward) = Λ R a , ((λ _ r → r) , (λ _ r → r)) ,
                                      (λ _ s → backward s) , (λ _ r → forward r)
