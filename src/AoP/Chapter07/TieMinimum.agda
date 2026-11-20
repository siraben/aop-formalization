{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.TieMinimum where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter08.Thinning using (Min)

-- Exercise 7.16. First minimize S on X, then minimize R among the
-- winners. In the single-pass specification R is consulted only when
-- the competing element is tied with the candidate under S.
module Law {A : Set} (S R : A ← A)
           (trans : ∀ {a b c} → S a b → S b c → S a c) where
  Tie : A ← A
  Tie a b = S a b × (S b a → R a b)

  combine : ∀ {a X} → Min R a (λ b → Min S b X) → Min Tie a X
  combine ((xa , best) , ties) = xa , λ b xb → best b xb ,
    (λ ba → ties b (xb , λ c xc → trans ba (best c xc)))

  separate : ∀ {a X} → Min Tie a X → Min R a (λ b → Min S b X)
  separate {a} (xa , best) = (xa , (λ b xb → fst (best b xb))) ,
    λ { b (xb , wins) → snd (best b xb) (wins a xa) }
