{-# OPTIONS --safe --without-K #-}
module AoP.RangeRotation where

open import AoP.Prelude
open import AoP.Relations
private variable A B C : Set

-- Range is a test on outputs: it fixes an output if some input reaches
-- it. The explicit diagonal equality makes this a coreflexive relation.
ran : (B ← A) → B ← B
ran {A = A} R b b′ = (b ≡ b′) × (Σ A λ a → R b a)

-- Exercise 4.16. An output c reached both directly by R and through
-- T then S determines a triangle (a,b,c). To recognize the same c,
-- start instead at b, following T backwards and R forwards, alongside
-- the direct S-edge. Only the order of the two witnesses changes.
module Rotate (R : C ← A) (S : C ← B) (T : B ← A) where
  forward : ran (R ⊓ (S ∘ T)) ⊆ ran ((R ∘ T ˘) ⊓ S)
  forward (eq , a , r , b , s , t) = eq , b , (a , r , t) , s

  backward : ran ((R ∘ T ˘) ⊓ S) ⊆ ran (R ⊓ (S ∘ T))
  backward (eq , b , (a , r , t) , s) = eq , a , r , b , s , t
