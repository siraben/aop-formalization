{-# OPTIONS --safe --without-K #-}
module AoP.Chapter01.Naturals where

open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import AoP.Common.Prelude

-- §1.2. Replace each successor by a step and zero by a seed.
foldn : ∀ {A : Set} → A → (A → A) → ℕ → A
foldn z s zero = z
foldn z s (suc n) = s (foldn z s n)

foldn-unique : ∀ {A : Set} (h : ℕ → A) z s → h zero ≡ z →
               (∀ n → h (suc n) ≡ s (h n)) → ∀ n → h n ≡ foldn z s n
foldn-unique h z s base step zero = base
foldn-unique h z s base step (suc n) = step n ∙ cong s (foldn-unique h z s base step n)

fact fib : ℕ → ℕ
fact zero = 1
fact (suc n) = suc n * fact n
fib zero = 0
fib (suc zero) = 1
fib (suc (suc n)) = fib n + fib (suc n)

-- The auxiliary state remembers the index which a plain fold does not expose.
factorials : ℕ → ℕ × ℕ
factorials = foldn (0 , 1) λ { (i , a) → suc i , suc i * a }

factorial-invariant : ∀ n → factorials n ≡ (n , fact n)
factorial-invariant zero = refl
factorial-invariant (suc n) rewrite factorial-invariant n = refl

-- Two adjacent entries suffice: the pair advances without recomputing either.
neighbours : ℕ → ℕ × ℕ
neighbours = foldn (0 , 1) λ { (a , b) → b , a + b }

fibonacci-invariant : ∀ n → neighbours n ≡ (fib n , fib (suc n))
fibonacci-invariant zero = refl
fibonacci-invariant (suc n) rewrite fibonacci-invariant n = refl

-- Exercise 1.6: the carrier itself can be a function space. The outer fold
-- computes a whole row of Ackermann's function from its preceding row.
ack : ℕ → ℕ → ℕ
ack = foldn suc λ row → foldn (row 1) row

ack-zero : ∀ y → ack 0 y ≡ suc y
ack-zero y = refl
ack-next-zero : ∀ x → ack (suc x) 0 ≡ ack x 1
ack-next-zero x = refl
ack-next-next : ∀ x y → ack (suc x) (suc y) ≡ ack x (ack (suc x) y)
ack-next-next x y = refl
