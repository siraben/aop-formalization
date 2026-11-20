{-# OPTIONS --safe --without-K #-}
module AoP.PartyPlanWork where

open import AoP.Prelude
open import AoP.PartyCachedPlan using (module Law)
open import AoP.PartyPlanTraversal using () renaming (module Law to Traversal)
open import AoP.Party using (module Planning)
open import AoP.Polynomial using (_⊎_)
open import AoP.Trees using (fork; grow; null)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Nat using (Nat; suc; _+_)

-- Exercise 7.44. Charge one table transition per constructor: at a
-- fork it compares two cached alternatives, at a forest link it joins
-- two pairs of entries, and at null it supplies the empty plans.
-- These are constant-size operations under sharing and unit-cost score
-- arithmetic, with correctness proofs excluded from the cost model.
module Count {E S : Set} (rating : E → S) (z : S) (add : S → S → S) (R : S → S → Set)
  (rid : ∀ a → R a a) (tr : ∀ {x y z} → R x y → R y z → R x z)
  (mono : ∀ {a b c d} → R a b → R c d → R (add a c) (add b d))
  (cmp : ∀ x y → R x y ⊎ R y x) where
  open Law rating z add R rid tr mono cmp
  open Planning rating z add R rid tr mono cmp using (score; total; omit)
  open Traversal rating z add R rid tr mono cmp using (nodes; links; visits)
  open Entry
  mutual
    build : ∀ t → (Entry (score {true} {t}) × Entry (score {false} {t})) × Nat
    build (fork e ts) with children ts
    ... | (i , o) , n = (skip e o , select e i o) , suc n
    children : ∀ ts → (Entry (total {true} {ts}) × Entry (total {false} {ts})) × Nat
    children null = rows null , 1
    children (grow t ts) with build t | children ts
    ... | (i , o) , n | (is , os) , m = (combine i is , combine o os) , suc (n + m)
  mutual
    cost-law : ∀ t → build t ≡ (table t , nodes t)
    cost-law (fork e ts) rewrite forest-law ts = refl
    forest-law : ∀ ts → children ts ≡ (rows ts , links ts)
    forest-law null = refl
    forest-law (grow t ts) rewrite cost-law t | forest-law ts = refl

  -- One pass to build and one to extract: exactly twice the input
  -- constructor count in this transition model.
  two-pass : ∀ t → snd (build t) + visits (plan (snd (fst (build t)))) ≡ nodes t + nodes t
  two-pass t rewrite cost-law t | Traversal.exact rating z add R rid tr mono cmp (plan (snd (table t))) = refl
