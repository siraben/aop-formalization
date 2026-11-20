{-# OPTIONS --safe --without-K #-}
module AoP.KnapsackFrontier where

open import AoP.Prelude
open import Agda.Builtin.Nat using (Nat; _+_)
open import AoP.NatOrder using (_≤_; rid; chain; sum-mono)
open import AoP.Thinning using (Thin)

-- §8.4 — Why is it safe to prune knapsack candidates before the bag is
-- full? Suppose two partial packs have (weight,value) (2,5) and (3,4).
-- The first can replace the second: anything that still fits alongside
-- the second also fits alongside the first, and the value cannot fall.
-- But (2,5) and (3,7) may both matter, depending on what comes next.
-- This module proves that replacement principle, not a sorting strategy.
Summary = Nat × Nat
weight = fst {A = Nat} {B = λ _ → Nat}
value = snd {A = Nat} {B = λ _ → Nat}

infix 4 _≼_
_≼_ : Summary → Summary → Set
p ≼ q = (weight p ≤ weight q) × (value q ≤ value p)

infixr 6 _⊞_
_⊞_ : Summary → Summary → Summary
(w , v) ⊞ (w′ , v′) = (w + w′) , (v + v′)

extend : ∀ i {p q} → p ≼ q → (i ⊞ p) ≼ (i ⊞ q)
extend (w , v) (light , rich) = sum-mono (rid w) light , sum-mono (rid v) rich

-- If Y is the unpruned set and X its frontier, an optimum over the
-- feasible part of X is an optimum over the feasible part of Y.
Feasible : Nat → (Summary → Set) → Summary → Set
Feasible cap X p = X p × (weight p ≤ cap)

Maximum : (Summary → Set) → Summary → Set
Maximum X p = X p × (∀ q → X q → value q ≤ value p)

preserve : ∀ cap X Y → Thin _≼_ X Y → ∀ p →
           Maximum (Feasible cap X) p → Maximum (Feasible cap Y) p
preserve cap X Y frontier p ((member , fits) , best) =
  (Thin.subset frontier member , fits) , λ where
    q (y , qfits) → bound q y qfits
  where
  bound : ∀ q → Y q → weight q ≤ cap → value q ≤ value p
  bound q y qfits with Thin.cover frontier q y
  ... | r , x , light , rich = chain rich (best r (x , chain light qfits))
