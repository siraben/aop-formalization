{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.RallyExpansion where

open import AoP.Common.Prelude
open import AoP.Chapter08.RallyDominance
open import AoP.Chapter08.RallyFrontier using (module Search)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Chapter08.ParagraphMinimum using (le?)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat)

module Law (cap s d : Nat) where
  open Leg cap s d
  open Search.Move cap s d
  keep-rest : ∀ a x rest {y} → y ∈ rest → y ∈ try a x rest
  keep-rest a x rest m with le? d (load a (State.fuel x))
  ... | inl ok = there m
  ... | inr no = m
  take : ∀ a x rest → Allowed a x → arrive a x ∈ try a x rest
  take a x rest legal with le? d (load a (State.fuel x))
  ... | inl ok = here
  ... | inr no with no legal
  ...   | ()

  -- Every legal action from every old candidate is enumerated,
  -- regardless of whether the other action at that station is legal.
  complete : ∀ xs {x} → x ∈ xs → ∀ a → Allowed a x → arrive a x ∈ expand xs
  complete (x ∷ xs) here pass ok = take pass x _ ok
  complete (x ∷ xs) here refill ok = keep-rest pass x _ (take refill x _ ok)
  complete (x ∷ xs) (there m) a ok = keep-rest pass x _ (keep-rest refill x _ (complete xs m a ok))
