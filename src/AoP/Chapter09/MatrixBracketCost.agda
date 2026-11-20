{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.MatrixBracketCost where

open import AoP.Common.Prelude
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

-- Exercise 9.10. Parenthesize a chain of compatible matrices to
-- minimize scalar multiplications using ordinary dense multiplication.
-- A product of an i-by-k result and a k-by-j result costs i*k*j and
-- has size i-by-j. Indexing by dimensions enforces compatibility.
data Plan : Nat → Nat → Set where
  matrix : ∀ i j → Plan i j
  mult : ∀ {i k j} → Plan i k → Plan k j → Plan i j

size : ∀ {i j} → Plan i j → Nat × Nat
size {i} {j} _ = i , j

cost : ∀ {i j} → Plan i j → Nat
cost (matrix _ _) = 0
cost (mult {i} {k} {j} l r) = cost l + cost r + ((i * k) * j)

-- Input dimensions 2×3, 3×4, 4×5. Both groupings produce a 2×5
-- matrix, but (AB)C uses 24+40 scalar multiplications versus 60+30.
A = matrix 2 3
B = matrix 3 4
C = matrix 4 5
left-cost : cost (mult (mult A B) C) ≡ 64
left-cost = refl
right-cost : cost (mult A (mult B C)) ≡ 90
right-cost = refl
