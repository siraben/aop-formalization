{-# OPTIONS --safe --without-K #-}
module AoP.LeftMinimumCount where

open import AoP.Prelude
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Complement using (⊥)
open import AoP.NatOrder using (_≤_; z≤; s≤; weaken)
open import Agda.Builtin.Nat using (Nat; suc)

-- Exercise 8.15. Process a nonempty input from left to right, with h
-- the first element of the current block. An extension costs nothing;
-- a new boundary costs one. Within a block every extension compares
-- against that same first element, exactly the left-minimum condition.
module Law {A : Set} (Q : A → A → Set) (rr : ∀ a → Q a a)
           (tr : ∀ {a b c} → Q a b → Q b c → Q a c)
           (test : ∀ a b → Q a b ⊎ (Q a b → ⊥)) where
  data Cuts (h : A) : List A → Nat → Set where
    done : Cuts h [] 0
    extend : ∀ {x xs n} → Q h x → Cuts h xs n → Cuts h (x ∷ xs) n
    split : ∀ {x xs n} → Cuts x xs n → Cuts h (x ∷ xs) (suc n)

  greedy : ∀ h xs → Σ Nat λ n → Cuts h xs n
  greedy h [] = 0 , done
  greedy h (x ∷ xs) with test h x
  ... | inl hx = _ , extend hx (snd (greedy h xs))
  ... | inr no = _ , split (snd (greedy x xs))

  -- Compare even when the two current blocks began at different
  -- heads: if the greedy head precedes the other head it can match
  -- every free extension. An extra competing split can only cost more.
  bound : ∀ {g h xs n} → Q g h → Cuts h xs n → fst (greedy g xs) ≤ n
  bound gh done = z≤
  bound {g} gh (extend {x} hx tail) with test g x
  ... | inl _ = bound gh tail
  ... | inr no with no (tr gh hx)
  ...   | ()
  bound {g} gh (split {x} tail) with test g x
  ... | inl gx = weaken (bound gx tail)
  ... | inr _ = s≤ (bound (rr x) tail)

  optimal : ∀ h xs {n} → Cuts h xs n → fst (greedy h xs) ≤ n
  optimal h xs = bound (rr h)
