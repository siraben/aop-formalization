{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.SelectionPairCost where

open import AoP.Common.Prelude
open import AoP.Chapter06.SelectionPairFold using (Pair; base; step; select)
open import AoP.Chapter06.SelectionSort using (length)
open import Agda.Builtin.Nat using (Nat; suc)

-- Count comparisons in the pair fold: the singleton base makes none,
-- and each step compares the next value with the current minimum once.
counted : Nat → List Nat → Pair × Nat
counted a [] = base a , 0
counted a (b ∷ bs) with counted b bs
... | p , n = step a p , suc n

exact : ∀ a xs → counted a xs ≡ (select a xs , length xs)
exact a [] = refl
exact a (b ∷ bs) rewrite exact b bs = refl

-- A duplicate still requires a comparison, even when the tied minima
-- give the same numeric result whichever occurrence is retained.
tie : counted 3 (1 ∷ 1 ∷ []) ≡ ((1 , 3 ∷ 1 ∷ []) , 2)
tie = refl
