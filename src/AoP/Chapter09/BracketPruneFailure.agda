{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.BracketPruneFailure where

open import AoP.Common.Prelude
open import AoP.Chapter01.Trees using (Tree; tip; bin)
open import AoP.Chapter09.Bracketing using (module Model)
open import AoP.Chapter09.BracketSpine using (options)
open import AoP.Chapter09.BracketEnumeration using (enumerate)
open import AoP.Chapter03.Horner using (map)
open import Agda.Builtin.Nat using (Nat; _*_)

-- Exercise 9.14. Test the tempting rule 'only keep the cheapest tree
-- for the current suffix'. Matrices have the indicated outer sizes;
-- adjacent dimensions match in every bracketing of this chain.
Dims = Nat × Nat
module M = Model (λ (p : Dims) → p) (λ l r → fst l , snd r)
                 (λ l r → fst l * snd l * snd r)
a b c d : Dims
a = 1 , 2
b = 2 , 1
c = 1 , 2
d = 2 , 3
cheap = bin (tip b) (bin (tip c) (tip d))
dear = bin (bin (tip b) (tip c)) (tip d)
suffix-trees : enumerate (b ∷ c ∷ d ∷ []) ≡ cheap ∷ dear ∷ []
suffix-trees = refl
suffix-costs : map M.cost (cheap ∷ dear ∷ []) ≡ 12 ∷ 16 ∷ []
suffix-costs = refl
-- Prepending a can open the suffix's left spine. The discarded suffix
-- admits a cost-10 tree, beating both extensions of the cost-12 suffix.
kept-costs : map M.cost (options a cheap) ≡ 18 ∷ 11 ∷ []
kept-costs = refl
lost-costs : map M.cost (options a dear) ≡ 22 ∷ 14 ∷ 10 ∷ []
lost-costs = refl
