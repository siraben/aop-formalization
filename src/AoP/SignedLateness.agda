{-# OPTIONS --safe --without-K #-}
module AoP.SignedLateness where

open import AoP.Prelude
open import AoP.Tardiness using (Job; job; elapsed)
open import AoP.Snoc using (Snoc; ε; _▻_)
open import AoP.SignedSegment using (_≤_; cmp; up; down; repeat; repeat-mono; down-mono)
open import AoP.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open Job

-- Exercise 10.10. Work in weighted time units: start at w*t and
-- subtract w*d. Integer predecessor crosses zero without truncation.
charge : Job → Nat → Int
charge j t = repeat (weight j * due j) down (pos (weight j * t))

data Peak : Set where
  bottom : Peak
  finite : Int → Peak
raise : Peak → Int → Peak
raise bottom q = finite q
raise (finite p) q with cmp p q
... | inl _ = finite q
... | inr _ = finite p

score : Snoc Job → Peak
score ε = bottom
score (xs ▻ j) = raise (score xs) (charge j (elapsed xs + duration j))

-- Both jobs finish early. Running the longer-deadline job first
-- changes the peak from -3 to -2, although either tardiness is zero.
a = job 1 4 1
b = job 1 8 1
first : score ((ε ▻ a) ▻ b) ≡ finite (negsuc 2)
first = refl
second : score ((ε ▻ b) ▻ a) ≡ finite (negsuc 1)
second = refl
