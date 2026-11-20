{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.ClosureIterate where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter06.Closure using (module Paths)

-- Exercise 6.33. An iterate records the starting vertex and the
-- number of steps, leaving the intermediate vertices unspecified.
-- The identity fold ignores the steps. The relational fold chooses
-- one edge for each `again`. Their shared input witnesses a path.
data Iterate (A : Set) : Set where
  once : A → Iterate A
  again : Iterate A → Iterate A

start : ∀ {A} → Iterate A → A
start (once a) = a
start (again i) = start i

module Law {A : Set} (R : A ← A) where
  open Paths R
  data Walk : A ← Iterate A where
    base : ∀ {a} → Walk a (once a)
    next : ∀ {a b i} → R b a → Walk a i → Walk b (again i)

  encode : ∀ {a b} → Star b a → Σ (Iterate A) λ i → Walk b i × (start i ≡ a)
  encode stop = once _ , base , refl
  encode (extend edge p) with encode p
  ... | i , w , eq = again i , next edge w , eq

  decode : ∀ {b i} → Walk b i → Star b (start i)
  decode base = stop
  decode (next edge w) = extend edge (decode w)

  sound : ∀ {a b} → (Σ (Iterate A) λ i → Walk b i × (start i ≡ a)) → Star b a
  sound (i , w , refl) = decode w
