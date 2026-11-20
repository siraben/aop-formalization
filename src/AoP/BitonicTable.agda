{-# OPTIONS --safe --without-K #-}
module AoP.BitonicTable where

open import AoP.Prelude
open import AoP.Bitonic
open import AoP.NatOrder using (_≤_; rid; chain; sum-mono; compare)
open import AoP.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat; _+_)

-- §8.6. Once city u has been assigned, one exposed end is u. The other
-- is an earlier city v. Store both orientations: directed edge costs
-- can make the outward and homeward subproblems different. Each layer
-- introduces one city and one extra pair of entries. Cache each route's
-- cost so choosing a successor takes two edge evaluations, two additions
-- and a comparison, independent of the length of the remaining route.
module DP {City : Set} (edge : City → City → Nat) (end : City) where
  open Tours edge
  record Cell (u v : City) (xs : List City) : Set where
    constructor cell
    field
      route : Route xs
      price : Nat
      value : cost u v end route ≡ price
      least : (q : Route xs) → price ≤ cost u v end q

  base : ∀ u v → Cell u v []
  base u v = cell close _ refl (λ { close → rid _ })

  update : ∀ u v x {xs} → Cell x v xs → Cell u x xs → Cell u v (x ∷ xs)
  update u v x (cell a ca va la) (cell b cb vb lb) with compare (edge u x + ca) (edge x v + cb)
  ... | inl le = cell (outward a) _ (cong (edge u x +_) va) λ where
    (outward q) → sum-mono (rid _) (la q)
    (homeward q) → chain le (sum-mono (rid _) (lb q))
  ... | inr ge = cell (homeward b) _ (cong (edge x v +_) vb) λ where
    (outward q) → chain ge (sum-mono (rid _) (la q))
    (homeward q) → sum-mono (rid _) (lb q)

  Pair : City → City → List City → Set
  Pair u v xs = Cell u v xs × Cell v u xs

  data Row (u : City) (xs : List City) : List City → Set where
    nil : Row u xs []
    cons : ∀ {v vs} → Pair u v xs → Row u xs vs → Row u xs (v ∷ vs)

  close-row : ∀ u vs → Row u [] vs
  close-row u [] = nil
  close-row u (v ∷ vs) = cons (base u v , base v u) (close-row u vs)

  -- The head pair (x,u)/(u,x) is shared by every update in the row.
  retreat : ∀ u x {xs vs} → Pair x u xs → Row x xs vs → Row u (x ∷ xs) vs
  retreat u x shared nil = nil
  retreat u x (xu , ux) (cons {v} (xv , vx) rest) =
    cons (update u v x xv ux , update v u x xu vx) (retreat u x (xu , ux) rest)

  table : ∀ u xs vs → Row u xs vs
  table u [] vs = close-row u vs
  table u (x ∷ xs) vs with table x xs (u ∷ vs)
  ... | cons shared rest = retreat u x shared rest

  tour-table : ∀ start xs → Cell start start xs
  tour-table start xs with table start xs (start ∷ [])
  ... | cons (c , _) nil = c
