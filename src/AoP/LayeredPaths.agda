{-# OPTIONS --safe --without-K #-}
module AoP.LayeredPaths where

open import AoP.Prelude
open import AoP.Thinning using (Thin)
open import AoP.Complement using (⊥)

-- §8.2 — Which partial routes may a shortest-path search discard?
-- Imagine a network drawn in columns. Each edge goes to the next column;
-- we build routes backwards, prepending a vertex to an existing suffix.
-- A suffix of cost 2 need not beat one of cost 5: reaching their starting
-- vertices might cost 10 and 1 respectively. If the starts coincide,
-- however, *the same edge* can extend either route. Then the cheaper
-- suffix stays cheaper. This is why a table groups candidates by start.
--
-- The proof below isolates this pruning step, independent of how a finite
-- table is stored. A path records actual edges; no edge is presumed to
-- exist. ExtendSet takes one step backwards from a layer of candidates.
module Network {V Cost : Set} (Edge : V → V → Set) (weight : ∀ {u v} → Edge u v → Cost)
               (zero : Cost) (_+_ : Cost → Cost → Cost) (_≤_ : Cost → Cost → Set)
               (mono : ∀ w {x y} → x ≤ y → (w + x) ≤ (w + y)) where
  data Path : V → Set where
    end : ∀ {v} → Path v
    via : ∀ {u v} → Edge u v → Path v → Path u

  cost : ∀ {v} → Path v → Cost
  cost end = zero
  cost (via e p) = weight e + cost p

  Layer : Set₁
  Layer = ∀ v → Path v → Set

  ExtendSet : Layer → Layer
  ExtendSet X u end = ⊥
  ExtendSet X u (via {v = v} e p) = X v p

  Prunes : Layer → Layer → Set
  Prunes X Y = ∀ v → Thin (λ p q → cost p ≤ cost q) (X v) (Y v)

  -- Thin.subset prevents inventing routes. Thin.cover supplies a cheaper
  -- suffix with the same start; monotonicity allows reusing the old edge.
  extend-thin : ∀ {X Y} → Prunes X Y → Prunes (ExtendSet X) (ExtendSet Y)
  Thin.subset (extend-thin t u) {end} ()
  Thin.subset (extend-thin t u) {via {v = v} e p} x = Thin.subset (t v) x
  Thin.cover (extend-thin t u) end ()
  Thin.cover (extend-thin t u) (via {v = v} e p) y with Thin.cover (t v) p y
  ... | q , x , le = via e q , x , mono (weight e) le
