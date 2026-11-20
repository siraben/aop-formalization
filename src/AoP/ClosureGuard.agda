{-# OPTIONS --safe --without-K #-}
module AoP.ClosureGuard where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Closure using (module Paths)
open import AoP.ClosureRuns using (module Runs)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Complement using (⊥)

-- Exercise 6.37. The restriction R ∘ ~C keeps edges whose source
-- fails the test C. The hypothesis R ∘ C ⊆ C says every discarded
-- edge is a self-loop. Use the run decomposition of exercise 6.36:
-- split at discarded edges, then concatenate the retained runs.
module Guard {A : Set} (R : A ← A) (C : A → Set)
             (test : ∀ x → C x ⊎ (C x → ⊥))
             (idle : ∀ {x y} → C x → R y x → y ≡ x) where
  Keep Skip : A ← A
  Keep y x = R y x × (C x → ⊥)
  Skip y x = R y x × C x
  module All = Paths R
  module K = Paths Keep
  module D = Runs Keep Skip

  tag : All.Star ⊆ D.U.Star
  tag All.stop = D.U.stop
  tag (All.extend {b = x} e p) with test x
  ... | inl c = D.U.extend (inr (e , c)) (tag p)
  ... | inr nc = D.U.extend (inl (e , nc)) (tag p)

  erase : D.Blocks.Star ⊆ K.Star
  erase D.Blocks.stop = K.stop
  erase (D.Blocks.extend (_ , (e , c) , run) before) with idle c e
  ... | refl = K.append (_ , run , erase before)

  restrict : All.Star ⊆ K.Star
  restrict p with D.split (tag p)
  ... | x , run , before = K.append (x , run , erase before)

  forget : K.Star ⊆ All.Star
  forget K.stop = All.stop
  forget (K.extend (e , _) p) = All.extend e (forget p)
