{-# OPTIONS --safe --without-K #-}
module AoP.ClosureFrontierInvariant where

open import AoP.Prelude
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Complement using (⊥)
open import AoP.Relations using (_←_)
open import AoP.Closure using (module Paths)

-- §6.7. A frontier search stores finished vertices P and newly found
-- vertices Q. Only Q must be expanded this round. Characterize the
-- answer by its upper bounds: it fits inside every edge-closed set
-- containing the seeds, and is contained in the reachable vertices.
module Search {A : Set} (R : A ← A) (seed : A → Set) where
  open Paths R using (Star; stop; extend)
  Reach : A → Set
  Reach y = Σ A λ x → seed x × Star y x
  record State (P Q : A → Set) : Set where
    field
      seeds : ∀ x → seed x → P x ⊎ Q x
      sound : ∀ x → P x ⊎ Q x → Reach x
      finished : ∀ {x y} → P x → R y x → P y ⊎ Q y
  start : State (λ _ → ⊥) seed
  State.seeds start x = inr
  State.sound start x (inl ())
  State.sound start x (inr s) = x , s , stop
  State.finished start ()
  module Round {P Q} (st : State P Q) where
    open State st
    Seen : A → Set
    Seen x = P x ⊎ Q x
    Fresh : A → Set
    Fresh y = (Σ A λ x → Q x × R y x) × (Seen y → ⊥)
    step : (∀ x → Seen x ⊎ (Seen x → ⊥)) → State Seen Fresh
    State.seeds (step dec) x s = inl (seeds x s)
    State.sound (step dec) x (inl h) = sound x h
    State.sound (step dec) y (inr ((x , q , edge) , _)) with sound x (inr q)
    ... | a , s , path = a , s , extend edge path
    State.finished (step dec) (inl p) edge = inl (finished p edge)
    State.finished (step dec) {x} {y} (inr q) edge with dec y
    ... | inl seen = inl seen
    ... | inr absent = inr ((x , q , edge) , absent)
    -- At an empty frontier P contains the seeds and is closed under
    -- R. Induction on a path now puts every reachable vertex in P.
    module Stop (empty : ∀ x → Q x → ⊥) where
      done : ∀ x → Seen x → P x
      done x (inl p) = p
      done x (inr q) with empty x q
      ... | ()
      follow : ∀ {a x} → seed a → Star x a → P x
      follow s stop = done _ (seeds _ s)
      follow s (extend edge path) = done _ (finished (follow s path) edge)
      complete : ∀ x → Reach x → P x
      complete x (a , s , path) = follow s path
      correct : ∀ x → P x → Reach x
      correct x p = sound x (inl p)
