{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.Bitonic where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; rid; chain; sum-mono; compare)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat; _+_)

-- §8.6. Cities arrive in left-to-right order. Start at the leftmost,
-- reach the rightmost, and return, visiting each interior city once.
-- Assign each interior city either to the outward leg or the return leg.
-- During a left-to-right scan, u and v are the exposed ends of those
-- legs. Putting x on the return leg pays x → v, NOT v → x: the tour
-- will traverse that leg in reverse order. Distances may be asymmetric.
module Tours {City : Set} (edge : City → City → Nat) where
  data Route : List City → Set where
    close : Route []
    outward homeward : ∀ {x xs} → Route xs → Route (x ∷ xs)

  cost : ∀ {xs} → City → City → City → Route xs → Nat
  cost u v end close = edge u end + edge end v
  cost u v end (outward {x} p) = edge u x + cost x v end p
  cost u v end (homeward {x} p) = edge x v + cost u x end p

  Best : City → City → City → List City → Set
  Best u v end xs = Σ (Route xs) λ p → (q : Route xs) → cost u v end p ≤ cost u v end q

  -- Reference recurrence: try both assignments and return the cheaper
  -- continuation together with a lower bound for every competitor. This
  -- version recomputes repeated endpoint pairs; it is not quadratic.
  solve : ∀ u v end xs → Best u v end xs
  solve u v end [] = close , λ { close → rid _ }
  solve u v end (x ∷ xs) with solve x v end xs | solve u x end xs
  ... | a , l | b , r with compare (edge u x + cost x v end a) (edge x v + cost u x end b)
  ...   | inl le = outward a , λ where
    (outward p) → sum-mono (rid _) (l p)
    (homeward p) → chain le (sum-mono (rid _) (r p))
  ...   | inr ge = homeward b , λ where
    (outward p) → chain ge (sum-mono (rid _) (l p))
    (homeward p) → sum-mono (rid _) (r p)

  tour : ∀ start interior end → Best start start end interior
  tour start interior end = solve start start end interior
