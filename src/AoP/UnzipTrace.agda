{-# OPTIONS --safe --without-K #-}
module AoP.UnzipTrace where

open import Agda.Builtin.Nat using (Nat; suc)
open import AoP.Prelude
open import AoP.Horner using (map)
open import AoP.ListMeet using (Align; cons; nil)
open import AoP.UnzipListLaw using (unzip; module Law)

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
