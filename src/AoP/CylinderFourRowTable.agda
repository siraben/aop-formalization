{-# OPTIONS --safe --without-K #-}
module AoP.CylinderFourRowTable where

open import AoP.Prelude
open import AoP.CylinderExample using (Row; top; upper; lower; bottom; up; down; entry-col; exit-col)
open import AoP.Cylinder using (module Grid)
open import AoP.CylinderCachedColumn using (module Table)
open Grid Row up down
open Table Row up down

-- Materialize a column as four fields. A function-only representation
-- can repeat a suffix search each time a row is looked up. Here each
-- update refers to the same previous tuple and projects its neighbours.
record Rim (c : Column) (cs : List Column) : Set where
  constructor rim
  field t : Cell c top cs
        u : Cell c upper cs
        l : Cell c lower cs
        b : Cell c bottom cs
get : ∀ {c cs} → Rim c cs → ∀ r → Cell c r cs
get v top = Rim.t v
get v upper = Rim.u v
get v lower = Rim.l v
get v bottom = Rim.b v
pack : ∀ {c cs} → (∀ r → Cell c r cs) → Rim c cs
pack f = rim (f top) (f upper) (f lower) (f bottom)

solve-rim : ∀ c cs → Rim c cs
solve-rim c [] = pack (end c)
solve-rim c (d ∷ ds) = let next = solve-rim d ds in pack (λ r → step c r d (get next))

-- Reuse the boundary-sensitive example. The top entry's cheapest
-- continuation wraps up to the bottom exit; the stored score includes
-- both visited cells. No second traversal is needed to read the score.
winner = Rim.t (solve-rim entry-col (exit-col ∷ []))
wraps : Cell.path winner ≡ rise exit
wraps = refl
cached : Cell.score winner ≡ 2
cached = refl
