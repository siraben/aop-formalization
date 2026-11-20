{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.CylinderEntry where

open import AoP.Common.Prelude
open import AoP.Chapter07.Cylinder
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Common.NatOrder using (_≤_; rid; chain; compare)

-- §7.4 allows the path to start anywhere on the entry rim. Supply its
-- nonempty enumeration; repeated entries are harmless. For each row the
-- fixed-entry solver already knows its cheapest continuation, so comparing
-- those minima suffices. This wrapper specifies correctness, not tabulation.
module Rim (Row : Set) (up down : Row → Row) where
  open Grid Row up down
  module Search (c : Column) (cs : List Column) where
    record Winner (rows : List Row) : Set where
      constructor win
      field
        entry : Row
        allowed : entry ∈ rows
        route : Path cs
        least : ∀ r → r ∈ rows → (p : Path cs) → cost c entry route ≤ cost c r p

    choose : ∀ r rs → Winner (r ∷ rs)
    choose r [] with solve c r cs
    ... | p , opt = win r here p λ { _ here q → opt q ; _ (there ()) }
    choose r (s ∷ ss) with solve c r cs | choose s ss
    ... | p , opt | win e valid t bound with compare (cost c r p) (cost c e t)
    ...   | inl le = win r here p λ where
      _ here q → opt q
      u (there m) q → chain le (bound u m q)
    ...   | inr ge = win e (there valid) t λ where
      _ here q → chain ge (opt q)
      u (there m) q → bound u m q
