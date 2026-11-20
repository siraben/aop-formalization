{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.GuardedBinaryThin where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_)
open import AoP.Chapter08.Thinning using (Pred; Thin)
open import AoP.Chapter08.ThinningFold using (module Lists)

-- Exercise 8.22, cons-list inputs. Each branch tests its own guard on
-- the old state *before* computing the new state. A dominating state
-- must keep each enabled branch enabled; only enabled outputs need to
-- preserve dominance. Neither branch needs to be enabled everywhere.
module Law {A B : Set} (Q : B ← B) (trans : ∀ {a b c} → Q a b → Q b c → Q a c)
           (seed : Pred B) (P G : A → B → Set) (f g : A → B → B)
           (keepP : ∀ x {a b} → Q a b → P x b → P x a)
           (keepG : ∀ x {a b} → Q a b → G x b → G x a)
           (stepP : ∀ x {a b} → Q a b → P x b → Q (f x a) (f x b))
           (stepG : ∀ x {a b} → Q a b → G x b → Q (g x a) (g x b)) where
  data Branch : B ← (A × B) where
    first : ∀ {x b} → P x b → Branch (f x b) (x , b)
    second : ∀ {x b} → G x b → Branch (g x b) (x , b)

  match : ∀ {x a b c} → Q a b → Branch c (x , b) → Σ B λ d → Branch d (x , a) × Q d c
  match {x} ab (first p) = _ , first (keepP x ab p) , stepP x ab p
  match {x} ab (second p) = _ , second (keepG x ab p) , stepG x ab p

  module T = Lists Q trans seed Branch match
  module Solver (table : List A → Pred B) (base : Thin Q (table []) seed)
                (prune : ∀ x xs → Thin Q (table (x ∷ xs)) (T.Next x (table xs))) where
    open T.Run table base prune public using (exact; correct)
