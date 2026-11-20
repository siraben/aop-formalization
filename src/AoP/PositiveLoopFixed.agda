{-# OPTIONS --safe --without-K #-}
module AoP.PositiveLoopFixed where

open import AoP.Prelude
open import AoP.Relations using (_←_; _⊆_; _∘_)
open import AoP.Shunting using (graph; Id)
open import AoP.RelationalSums using (_⊕_; left; right)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- §6.5. Both programs defining a recursion layer are total functions.
-- Positive inputs recur on themselves; only zero reaches a base case.
produce : Nat → ⊤ ⊎ Nat
produce zero = inl tt
produce (suc n) = inr (suc n)
consume : ⊤ ⊎ Nat → Nat
consume (inl tt) = 0
consume (inr n) = n

-- Map X over the recursive child only, then apply the consumer.
data Layer (X : Nat ← Nat) : Nat ← Nat where
  base : Layer X 0 0
  loop : ∀ {b n} → X b (suc n) → Layer X b (suc n)

-- Expand the graph composite to justify the two simplified cases.
Composite : (Nat ← Nat) → Nat ← Nat
Composite X = graph consume ∘ ((Id ⊕ X) ∘ graph produce)
expand : ∀ {X} → Layer X ⊆ Composite X
expand base = inl tt , refl , inl tt , left refl , refl
expand (loop p) = inr _ , refl , inr _ , right p , refl
contract : ∀ {X} → Composite X ⊆ Layer X
contract {a = zero} (_ , refl , _ , left refl , refl) = base
contract {a = suc n} (_ , refl , _ , right p , refl) = loop p

data ZeroOnly : Nat ← Nat where
  done : ZeroOnly 0 0
roll : Layer ZeroOnly ⊆ ZeroOnly
roll base = done
roll (loop ())
unroll : ZeroOnly ⊆ Layer ZeroOnly
unroll done = base
least : ∀ (X : Nat ← Nat) → Layer X ⊆ X → ZeroOnly ⊆ X
least X closed done = closed base

-- Identity also obeys the equation, but has the additional edge 1→1.
id-roll : Layer _≡_ ⊆ _≡_
id-roll base = refl
id-roll (loop eq) = eq
id-unroll : _≡_ ⊆ Layer _≡_
id-unroll {zero} refl = base
id-unroll {suc n} refl = loop refl
data Empty : Set where
partial : (Σ Nat (λ b → ZeroOnly b 1)) → Empty
partial (_ , ())
