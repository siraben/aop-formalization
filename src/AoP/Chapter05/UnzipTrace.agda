{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.UnzipTrace where

open import Agda.Builtin.Nat using (Nat; suc)
open import AoP.Common.Prelude
open import AoP.Chapter03.Horner using (map)
open import AoP.Chapter05.ListMeet using (Align; cons; nil)
open import AoP.Chapter05.UnzipListLaw using (unzip; module Law)

-- Two independent nondeterministic choices at each position. The
-- requested left output changes only at the head, the right only at
-- the tail. Reconstruct the intermediate pairs for exercise 5.10.
data Choice : Nat → Nat → Set where
  keep : ∀ {x} → Choice x x
  bump : ∀ {x} → Choice (suc x) x
open Law Choice Choice
input : List (Nat × Nat)
input = (0 , 3) ∷ (2 , 1) ∷ []
lefts : Align Choice (1 ∷ 2 ∷ []) (map fst input)
lefts = cons bump (cons keep nil)
rights : Align Choice (3 ∷ 2 ∷ []) (map snd input)
rights = cons keep (cons bump nil)
paired = rebuild input lefts rights
result : fst paired ≡ (1 , 3) ∷ (2 , 2) ∷ []
result = refl
projected : unzip (fst paired) ≡ ((1 ∷ 2 ∷ []) , (3 ∷ 2 ∷ []))
projected = fst (snd paired)
