{-# OPTIONS --safe --without-K #-}
module AoP.KnapsackFrontier where

open import AoP.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import AoP.NatOrder using (_≤_; rid; chain; sum-mono)
open import AoP.Thinning using (Thin)
open import AoP.Bump using (module Prune)
open import AoP.NatOrder using (z≤; s≤)
open import AoP.Subsequences using (_∈_)

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

-- Turn the criterion into a comparison for the adjacent bump algorithm
-- of §8.3. If neither orientation is certified, both packs must survive.
module B = Prune _≼_ (λ p → rid _ , rid _) (λ p q → chain (fst p) (fst q) , chain (snd q) (snd p))

data Test (P : Set) : Set where
  proved : P → Test P
  unknown : Test P

test : ∀ m n → Test (m ≤ n)
test zero n = proved z≤
test (suc m) zero = unknown
test (suc m) (suc n) with test m n
... | proved le = proved (s≤ le)
... | unknown = unknown

dominates : ∀ p q → Test (p ≼ q)
dominates p q with test (weight p) (weight q) | test (value q) (value p)
... | proved light | proved rich = proved (light , rich)
... | _ | _ = unknown

order : ∀ p q → B.Comparison p q
order p q with dominates p q | dominates q p
... | proved pq | _ = B.first pq
... | unknown | proved qp = B.second qp
... | unknown | unknown = B.retain

module Sweep = B.Algorithm order

-- One pass may leave nonadjacent dominated entries, but never loses the
-- optimum. This is a certified pruning pass, not a full sorted frontier.
sweep-optimum : ∀ cap xs p → Maximum (Feasible cap (_∈ Sweep.thinlist xs)) p →
                Maximum (Feasible cap (_∈ xs)) p
sweep-optimum cap xs = preserve cap _ _ (Sweep.correct xs)
