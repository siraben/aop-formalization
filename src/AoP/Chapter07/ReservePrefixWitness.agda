{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.ReservePrefixWitness where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (Fold; nil; cons)
open import AoP.Chapter07.ReservePrefixGreedy using (Seed; Next; stop; more; module Floor; module Ceiling)
open import AoP.Chapter07.SignedSegment using (module M; _≤_)
open import AoP.Chapter08.Thinning using (Min)
open import Agda.Builtin.Int using (Int; pos)

-- The stop branch ignores its recursive result, but a relational fold
-- still needs a witness for the tail. Stopping at every remaining cell
-- supplies that witness for every input, including an empty one.
zeros : ∀ ts → Fold Seed Next (pos 0) ts
zeros [] = nil refl
zeros (_ ∷ ts) = cons stop (zeros ts)

prefix : ∀ {ts x} → Fold Seed Next x ts → M.Prefix ts x
prefix (nil refl) = M.empty
prefix (cons stop _) = M.empty
prefix (cons more p) = M.extend (prefix p)

run : ∀ {ts x} → M.Prefix ts x → Fold Seed Next x ts
run (M.empty {xs}) = zeros xs
run (M.extend p) = cons more (run p)

-- The extrema are attained by actual prefixes and bound all of them.
floor : ∀ ts → Min _≤_ (fst (Floor.run ts)) (M.Prefix ts)
floor ts with Floor.optimum ts
... | p , bound = prefix p , λ x q → bound x (run q)
ceiling : ∀ ts → Min (λ x y → y ≤ x) (fst (Ceiling.run ts)) (M.Prefix ts)
ceiling ts with Ceiling.optimum ts
... | p , bound = prefix p , λ x q → bound x (run q)
