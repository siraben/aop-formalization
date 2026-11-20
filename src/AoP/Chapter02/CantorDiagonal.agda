{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.CantorDiagonal where

open import AoP.Common.Prelude
open import AoP.Chapter04.Complement using (⊥)

-- Exercise 2.37. If an initial powerset algebra existed, Lambek's
-- isomorphism would encode subsets as elements and decode every code
-- back to its subset. The diagonal subset defeats any such decoder.
-- Formulate the specific obstruction using predicates and membership
-- equivalence. Predicates on a small set live one universe higher; we
-- do not silently assume a small powerset endofunctor on Agda's Set.
module Diagonal (A : Set) (decode : A → A → Set) where
  diagonal : A → Set
  diagonal a = decode a a → ⊥

  -- No element represents this particular subset: specializing both
  -- membership implications at the alleged code gives a contradiction.
  missing : (k : A) → (∀ a → decode k a → diagonal a) →
            (∀ a → diagonal a → decode k a) → ⊥
  missing k out into = absent (into k absent)
    where
    absent : diagonal k
    absent member = out k member member

  no-encoding : (encode : (A → Set) → A) →
                (∀ p a → decode (encode p) a → p a) →
                (∀ p a → p a → decode (encode p) a) → ⊥
  no-encoding encode out into = missing (encode diagonal) (out diagonal) (into diagonal)
