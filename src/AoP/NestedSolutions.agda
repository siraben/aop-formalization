{-# OPTIONS --safe --without-K #-}
module AoP.NestedSolutions where

open import AoP.Prelude
open import AoP.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat; suc)

-- Exercise 1.2. Use natural subtraction, with predecessor of zero
-- equal to zero. A constant row ignores the nested call completely.
-- The positive columns of row zero can also return any fixed positive
-- value: the inner call then lands in that same part of row zero.
pred : Nat → Nat
pred 0 = 0
pred (suc n) = n

record Solution (m : Nat → Nat → Nat) : Set where
  field diagonal : ∀ x → m x x ≡ suc x
        nested : ∀ x y → (x ≡ y → ⊥) → m x y ≡ m x (m (pred x) (suc y))

row : Nat → Nat → Nat → Nat
row k 0 0 = 1
row k 0 (suc y) = suc k
row k (suc x) y = suc (suc x)

solves : ∀ k → Solution (row k)
Solution.diagonal (solves k) 0 = refl
Solution.diagonal (solves k) (suc x) = refl
Solution.nested (solves k) 0 0 ne with ne refl
... | ()
Solution.nested (solves k) 0 (suc y) ne = refl
Solution.nested (solves k) (suc x) y ne = refl

-- At (0,1) these two solutions give 1 and 2 respectively.
different : ((x y : Nat) → row 0 x y ≡ row 1 x y) → ⊥
different eq with eq 0 1
... | ()
