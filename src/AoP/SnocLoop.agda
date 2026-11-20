{-# OPTIONS --safe --without-K #-}
module AoP.SnocLoop where

open import AoP.Prelude
open import AoP.Snoc using (Snoc; ε; _▻_; foldl)
open import AoP.Polynomial using (_⊎_; inl; inr)
private variable A B : Set

-- Exercise 3.50. Process a snoc list from its last element towards
-- the front. Each step updates the state before visiting the prefix.
-- The fold carrier consists of functions on states: the prefix waits
-- for the state produced by the last element.
module Loop {A B : Set} (h : A × B → B) where
  loop : Snoc A × B → B
  loop (xs , b) = foldl (λ s → s) (λ k a s → k (h (a , s))) xs b

  Layer = ⊤ ⊎ (Snoc A × A)
  build : Layer → Snoc A
  build (inl _) = ε
  build (inr (xs , a)) = xs ▻ a

  rhs : (Snoc A × B → B) → Layer → B → B
  rhs k (inl _) b = b
  rhs k (inr (xs , a)) b = k (xs , h (a , b))

  Equation : (Snoc A × B → B) → Set
  Equation k = ∀ t b → k (build t , b) ≡ rhs k t b

  solves : Equation loop
  solves (inl _) b = refl
  solves (inr _) b = refl

  unique : (k : Snoc A × B → B) → Equation k → ∀ xs b → k (xs , b) ≡ loop (xs , b)
  unique k law ε b = law (inl tt) b
  unique k law (xs ▻ a) b = begin
    k (xs ▻ a , b) ≡⟨ law (inr (xs , a)) b ⟩
    k (xs , h (a , b)) ≡⟨ unique k law xs (h (a , b)) ⟩
    loop (xs ▻ a , b) ∎
