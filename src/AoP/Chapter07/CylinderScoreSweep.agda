{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.CylinderScoreSweep where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; rid; chain; sum-mono)
open import AoP.Chapter07.CylinderFiniteRim using (Row; up; down)
open import AoP.Chapter07.CylinderWindow using (Vec; nil; cons; at; module Scan)
open import AoP.Chapter07.Cylinder using (module Grid)
open import AoP.Chapter07.CylinderCachedColumn using (module Table)
open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import AoP.Common.NatOrder using (compare)
open import AoP.Chapter02.Polynomial using (inl; inr)

-- Add two columns by walking them in lockstep: no indexed lookups.
plus : ∀ {n} → Vec Nat n → Vec Nat n → Vec Nat n
plus nil nil = nil
plus (cons a as) (cons b bs) = cons (a + b) (plus as bs)
plus-at : ∀ {n} (a b : Vec Nat n) i → at (plus a b) i ≡ at a i + at b i
plus-at (cons x xs) (cons y ys) Row.top = refl
plus-at (cons x xs) (cons y ys) (Row.below i) = plus-at xs ys i

-- Scan a materialized first column directly. Cache the winning score
-- as well as its row, so we never re-index the tail to read its value.
record Cheapest {n} (v : Vec Nat (suc n)) : Set where
  constructor found
  field value : Nat
        start : Row (suc n)
        attained : value ≡ at v start
        least : ∀ i → value ≤ at v i

cheapest : ∀ {n} (v : Vec Nat (suc n)) → Cheapest v
cheapest (cons x nil) = found x Row.top refl λ { Row.top → rid _ ; (Row.below ()) }
cheapest (cons x tail@(cons y ys)) with cheapest tail
... | found m i exact bound with compare x m
...   | inl xm = found x Row.top refl (λ { Row.top → rid _ ; (Row.below j) → chain xm (bound j) })
...   | inr mx = found m (Row.below i) exact (λ { Row.top → mx ; (Row.below j) → bound j })

module Solve (n : Nat) where
  open Grid (Row (suc n)) up down using (Column; Path; cost; rise; stay; fall; exit)
  open Table (Row (suc n)) up down using (Move; U; S; D; row; extend; charge; pick)
  Col = Vec Nat (suc n)
  triple : Nat → Nat → Nat → Move → Nat
  triple u s d U = u
  triple u s d S = s
  triple u s d D = d
  min3 : Nat → Nat → Nat → Nat
  min3 u s d = let f = triple u s d in f (fst (pick f))
  module W = Scan min3
  update : Col → Col → Col
  update c tail = plus c (W.cyclic tail)
  scores : Col → List Col → Col
  scores c [] = c
  scores c (d ∷ ds) = update c (scores d ds)

  -- Interpret a vector input as the column functions used by the path
  -- specification. Neither conversion nor proof indexing occurs in scores.
  cols : List Col → List Column
  cols [] = []
  cols (d ∷ ds) = at d ∷ cols ds
  Best : ∀ c ds → Col → Set
  Best c ds v = ∀ r → Σ (Path (cols ds)) λ p → (at v r ≡ cost (at c) r p) ×
    ((q : Path (cols ds)) → at v r ≤ cost (at c) r q)

  step : ∀ c d ds t → Best d ds t → Best c (d ∷ ds) (update c t)
  step c d ds t good r = witness (pick f) (plus-at c (W.cyclic t) r ∙ cong (at c r +_) (W.correct t r))
    where
      f = triple (at t (up r)) (at t r) (at t (down r))
      lookup : ∀ m → f m ≡ at t (row m r)
      lookup U = refl
      lookup S = refl
      lookup D = refl
      witness : (w : Σ Move λ m → ∀ h → f m ≤ f h) → at (update c t) r ≡ at c r + f (fst w) →
        Σ (Path (cols (d ∷ ds))) λ p → (at (update c t) r ≡ cost (at c) r p) ×
          ((q : Path (cols (d ∷ ds))) → at (update c t) r ≤ cost (at c) r q)
      witness (m , least) eq = extend m p , (eq ∙ cong (at c r +_) (lookup m ∙ exact) ∙ charge (at c) r (at d) m p) , lower
        where p = fst (good (row m r))
              exact = fst (snd (good (row m r)))
              bound : ∀ h (q : Path (cols ds)) → at (update c t) r ≤ at c r + cost (at d) (row h r) q
              bound h q rewrite eq = sum-mono (rid _) (chain (least h) (tail-bound h q))
                where tail-bound : ∀ k (z : Path (cols ds)) → f k ≤ cost (at d) (row k r) z
                      tail-bound k z rewrite lookup k = snd (snd (good (row k r))) z
              lower : (q : Path (cols (d ∷ ds))) → at (update c t) r ≤ cost (at c) r q
              lower (rise q) = bound U q
              lower (stay q) = bound S q
              lower (fall q) = bound D q

  correct : ∀ c ds → Best c ds (scores c ds)
  correct c [] r = exit , refl , (λ { exit → rid _ })
  correct c (d ∷ ds) = step c d ds (scores d ds) (correct d ds)

  -- A single final scan removes the fixed-start restriction. Compose
  -- the first-column minimum with the bound supplied by each row.
  optimum : ∀ c ds → Nat
  optimum c ds = Cheapest.value (cheapest (scores c ds))
  global : ∀ c ds → Σ (Row (suc n)) λ r → Σ (Path (cols ds)) λ p →
    (optimum c ds ≡ cost (at c) r p) × (∀ j (q : Path (cols ds)) → optimum c ds ≤ cost (at c) j q)
  global c ds with cheapest (scores c ds)
  ... | found m r eq lower = r , p , (eq ∙ exact) , (λ j q → chain (lower j) (snd (snd (correct c ds j)) q))
    where p = fst (correct c ds r)
          exact = fst (snd (correct c ds r))

-- The cheap cells sit at opposite ends of successive columns. The
-- top entry uses the upward wrap; the other starts cost at least 10.
module Trace where
  open Solve 3
  four : Nat → Nat → Nat → Nat → Col
  four a b c d = cons a (cons b (cons c (cons d nil)))
  entry = four 1 9 9 9
  finish = four 9 9 9 1
  row-scores : scores entry (finish ∷ []) ≡ four 2 18 10 10
  row-scores = refl
  minimum : optimum entry (finish ∷ []) ≡ 2
  minimum = refl
