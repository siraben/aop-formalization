{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.EmptyRelationTargets where

open import AoP.Common.Prelude
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter02.EmptyTargets using (InitialSource)
open import AoP.Chapter04.Relations using (_←_; _⊆_; _∘_)
open import AoP.Chapter04.Shunting using (Id)
open import Agda.Builtin.Bool using (Bool; true)

-- Exercise 2.21, Rel. Every target, including the empty type, admits
-- the nowhere-defined relation from Bool. Its source is inhabited
-- and no composite through it can contain the identity pair at true.
module Law (A : Set) where
  zero : A ← Bool
  zero _ _ = ⊥

  no-left-inverse : (S : Bool ← A) → (Id ⊆ S ∘ zero) → ⊥
  no-left-inverse S section = snd (snd (section {true} refl))

  -- An invertible relation must at least have this half-inverse law.
  data Alternative (X : Set) (R : A ← X) : Set₁ where
    initial : InitialSource X → Alternative X R
    inverse : (S : X ← A) → Id ⊆ S ∘ R → Alternative X R

  impossible : ((X : Set) (R : A ← X) → Alternative X R) → ⊥
  impossible test with test Bool zero
  ... | initial empty = empty true
  ... | inverse s sec = no-left-inverse s sec
