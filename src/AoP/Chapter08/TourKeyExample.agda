{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.TourKeyExample where

open import AoP.Common.Prelude
open import AoP.Chapter08.TourKeyLayer using (module Keys)
open import AoP.Chapter03.Horner using (map)
open import AoP.Chapter01.Naturality using (_++_)
open import Agda.Builtin.Nat using (Nat; _==_)
open import Agda.Builtin.Bool using (Bool; true; false)
open Keys Nat

-- Exercise 8.25. Follow keys alone: picking any cheapest tour in a
-- block of identical keys leaves that same key. Starting at (4,4),
-- processing successive cities exposes two repeated blocks at the
-- third extension, one from each stream. No edge costs are needed.
same : Key → Key → Bool
same (a , b) (c , d) with a == c
... | false = false
... | true = b == d
push : Key → List Key → List Key
push p [] = p ∷ []
push p (q ∷ qs) with same p q
... | true = q ∷ qs
... | false = p ∷ q ∷ qs
compact : List Key → List Key
compact [] = []
compact (p ∷ ps) = push p (compact ps)
expand : Nat → List Key → List Key
expand b ps = map (left b) ps ++ map (right b) ps
layer₁ = compact (expand 3 ((4 , 4) ∷ []))
layer₂ = compact (expand 2 layer₁)
raw : expand 1 layer₂ ≡ (4 , 1) ∷ (3 , 1) ∷ (2 , 1) ∷ (2 , 1) ∷ (1 , 2) ∷ (1 , 2) ∷ (1 , 3) ∷ (1 , 4) ∷ []
raw = refl
survive : compact (expand 1 layer₂) ≡ (4 , 1) ∷ (3 , 1) ∷ (2 , 1) ∷ (1 , 2) ∷ (1 , 3) ∷ (1 , 4) ∷ []
survive = refl
