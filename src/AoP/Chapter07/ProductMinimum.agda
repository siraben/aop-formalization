{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.ProductMinimum where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter08.Thinning using (Min)

-- Exercise 7.15. Fix an input i and consider all independent choices
-- of an S-result and a T-result. Pairing a minimum of each fibre
-- yields a minimum among those pairs under componentwise comparison.
module Pair {I A B : Set} (S : A ← I) (T : B ← I)
            (R : A ← A) (Q : B ← B) where
  choices : I → A × B → Set
  choices i p = S (fst p) i × T (snd p) i

  componentwise : (A × B) ← (A × B)
  componentwise p q = R (fst p) (fst q) × Q (snd p) (snd q)

  pair-min : ∀ i a b → Min R a (λ x → S x i) → Min Q b (λ y → T y i) →
             Min componentwise (a , b) (choices i)
  pair-min i a b (sa , bestA) (tb , bestB) = (sa , tb) ,
    λ { (x , y) (sx , ty) → bestA x sx , bestB y ty }
