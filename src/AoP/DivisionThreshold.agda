{-# OPTIONS --safe --without-K #-}
module AoP.DivisionThreshold where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; z≤; s≤)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_; div-helper)

-- Audit the primitive used by cshift and halve. With countdown j,
-- reaching the first quotient unit consumes j+1 ticks; each further
-- unit consumes k+1 ticks. The accumulator only shifts the quotient.
private
  advance : ∀ a k n j → div-helper (suc a) k n j ≡ suc (div-helper a k n j)
  advance a k 0 j = refl
  advance a k (suc n) 0 = advance (suc a) k n k
  advance a k (suc n) (suc j) = advance a k n j

need : Nat → Nat → Nat → Nat
need k j 0 = 0
need k j (suc t) = suc (j + t * suc k)

sound : ∀ k n j t → t ≤ div-helper 0 k n j → need k j t ≤ n
sound k n j 0 p = z≤
sound k 0 j (suc t) ()
sound k (suc n) 0 (suc t) p rewrite advance 0 k n k with p
... | s≤ q = s≤ (next t q)
  where next : ∀ t → t ≤ div-helper 0 k n k → t * suc k ≤ n
        next 0 q = z≤
        next (suc t) q = sound k n k (suc t) q
sound k (suc n) (suc j) (suc t) p = s≤ (sound k n j (suc t) p)

complete : ∀ k n j t → need k j t ≤ n → t ≤ div-helper 0 k n j
complete k n j 0 p = z≤
complete k 0 j (suc t) ()
complete k (suc n) 0 (suc t) (s≤ p) rewrite advance 0 k n k = s≤ (next t p)
  where next : ∀ t → t * suc k ≤ n → t ≤ div-helper 0 k n k
        next 0 p = z≤
        next (suc t) p = complete k n k (suc t) p
complete k (suc n) (suc j) (suc t) (s≤ p) = complete k n j (suc t) p
