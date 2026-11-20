{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.KnapsackPackBridge where

open import AoP.Common.Prelude
open import AoP.Chapter08.Knapsack using (module Packing)
open import AoP.Chapter08.KnapsackFrontier using (Summary; _⊞_) renaming (weight to wt; value to val)
import AoP.Chapter08.KnapsackTableCoverage as Coverage
import AoP.Chapter08.KnapsackGuardStep as Guard
open import AoP.Chapter08.KnapsackHead using (module Solver)
open import AoP.Chapter03.Horner using (map)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; rid; chain; weaken)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _-_)

-- Bridge the sorted summary table to the reference specification on
-- original items. In particular, items with identical summaries still
-- occupy distinct slots: replay each decision against that input slot.
module Law {Item : Set} (weight value : Item → Nat) where
  open Packing weight value
  item : Item → Summary
  item x = weight x , value x
  private
    left : ∀ w n → w ≤ w + n
    left 0 n = z≤
    left (suc w) n = s≤ (left w n)
    tail-fit : ∀ w n c → w + n ≤ c → n ≤ c - w
    tail-fit 0 n c p = p
    tail-fit (suc w) n (suc c) (s≤ p) = tail-fit w n c p
    combine : ∀ w n c → w ≤ c → n ≤ c - w → w + n ≤ c
    combine 0 n c f p = p
    combine (suc w) n (suc c) (s≤ f) p = s≤ (combine w n c f p)
    smaller : ∀ c w → c - w ≤ c
    smaller c 0 = rid c
    smaller 0 (suc w) = z≤
    smaller (suc c) (suc w) = weaken (smaller c w)
    fits : ∀ {c is p} → Coverage.Search.Run c is p → wt p ≤ c
    fits Coverage.Search.empty = z≤
    fits (Coverage.Search.more h Guard.skip) = fits h
    fits (Coverage.Search.more h (Guard.take f)) = f
    widen : ∀ {c d is p} → c ≤ d → Coverage.Search.Run c is p → Coverage.Search.Run d is p
    widen le Coverage.Search.empty = Coverage.Search.empty
    widen le (Coverage.Search.more h Guard.skip) = Coverage.Search.more (widen le h) Guard.skip
    widen le (Coverage.Search.more h (Guard.take f)) = Coverage.Search.more (widen le h) (Guard.take (chain f le))

  encode : ∀ {c xs} (q : Pack c xs) → Σ Summary λ p → Coverage.Search.Run c (map item xs) p × (val p ≡ worth q)
  encode empty = _ , Coverage.Search.empty , refl
  encode (skip q) with encode q
  ... | p , h , eq = p , Coverage.Search.more h Guard.skip , eq
  encode {c} (take {x = x} f q) with encode q
  ... | p , h , eq = _ , Coverage.Search.more (widen (smaller c (weight x)) h) (Guard.take (combine (weight x) (wt p) c f (fits h))) , cong (value x +_) eq

  replay : ∀ c xs {d p} → Coverage.Search.Run d (map item xs) p → wt p ≤ c → Σ (Pack c xs) λ q → worth q ≡ val p
  replay c [] Coverage.Search.empty f = empty , refl
  replay c (x ∷ xs) (Coverage.Search.more h Guard.skip) f with replay c xs h f
  ... | q , eq = skip q , eq
  replay c (x ∷ xs) (Coverage.Search.more {p = p} h (Guard.take _)) f with replay (c - weight x) xs h (tail-fit (weight x) (wt p) c f)
  ... | q , eq = take (chain (left (weight x) (wt p)) f) q , cong (value x +_) eq

  solve-pack : ∀ c xs → Best c xs
  solve-pack c xs with Solver.solve c (map item xs)
  ... | p , h , best with replay c xs h (fits h)
  ...   | q , refl = q , bound
    where bound : ∀ r → worth r ≤ worth q
          bound r with encode r
          ... | s , run , refl = best run
