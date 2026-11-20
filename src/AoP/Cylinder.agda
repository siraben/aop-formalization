{-# OPTIONS --safe --without-K #-}
module AoP.Cylinder where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; rid; chain; sum-mono; compare)
open import AoP.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat; _+_)

-- §7.4. A grid wraps at its top and bottom. From a cell the next column
-- may be entered one row above, at the same row, or one row below. The
-- cost includes every visited cell, including the first and last. Looking
-- only at the next cell is unsound: its continuation may be expensive.
-- Instead compute an optimal suffix for each of the three possible moves.
module Grid (Row : Set) (up down : Row → Row) where
  Column = Row → Nat
  data Path : List Column → Set where
    exit : Path []
    rise stay fall : ∀ {c cs} → Path cs → Path (c ∷ cs)

  -- c is the current column; cs contains the columns still to visit.
  cost : ∀ {cs} → Column → Row → Path cs → Nat
  cost c r exit = c r
  cost c r (rise {d} p) = c r + cost d (up r) p
  cost c r (stay {d} p) = c r + cost d r p
  cost c r (fall {d} p) = c r + cost d (down r) p

  module From (c : Column) (r : Row) (cs : List Column) where
    Best = Σ (Path cs) λ p → (q : Path cs) → cost c r p ≤ cost c r q

  -- Select the least of three already solved suffixes. The caller may
  -- represent rows cyclically; the proof uses no ordering of row labels.
  solve : ∀ c r cs → From.Best c r cs
  solve c r [] = exit , λ { exit → rid _ }
  solve c r (d ∷ ds) with solve d (up r) ds | solve d r ds | solve d (down r) ds
  ... | a , l | b , m | e , n with compare (cost d (up r) a) (cost d r b)
  ...   | inl ab with compare (cost d (up r) a) (cost d (down r) e)
  ...     | inl ae = rise a , λ where
      (rise p) → sum-mono (rid _) (l p)
      (stay p) → sum-mono (rid _) (chain ab (m p))
      (fall p) → sum-mono (rid _) (chain ae (n p))
  ...     | inr ea = fall e , λ where
      (rise p) → sum-mono (rid _) (chain ea (l p))
      (stay p) → sum-mono (rid _) (chain ea (chain ab (m p)))
      (fall p) → sum-mono (rid _) (n p)
  solve c r (d ∷ ds) | a , l | b , m | e , n | inr ba with compare (cost d r b) (cost d (down r) e)
  ... | inl be = stay b , λ where
      (rise p) → sum-mono (rid _) (chain ba (l p))
      (stay p) → sum-mono (rid _) (m p)
      (fall p) → sum-mono (rid _) (chain be (n p))
  ... | inr eb = fall e , λ where
      (rise p) → sum-mono (rid _) (chain eb (chain ba (l p)))
      (stay p) → sum-mono (rid _) (chain eb (m p))
      (fall p) → sum-mono (rid _) (n p)
