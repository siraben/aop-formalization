{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.RallyReachable where

open import AoP.Common.Prelude
open import AoP.Chapter08.RallyDominance
open import AoP.Chapter08.RallyFrontier using (module Pruning; module Search)
open import AoP.Chapter08.RallyRoute using (module Routes; station)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Chapter08.ParagraphMinimum using (le?)
open import AoP.Chapter08.Thinning using (Thin)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import Agda.Builtin.Nat using (Nat)

module Sound (cap : Nat) where
  open Search cap
  open Routes cap
  module Step (s d : Nat) where
    open Move s d
    open Leg cap s d
    undo : ∀ a x rest {y} → y ∈ try a x rest → (Allowed a x × (arrive a x ≡ y)) ⊎ (y ∈ rest)
    undo a x rest m with le? d (load a (State.fuel x))
    ... | inr no = inr m
    ... | inl ok with m
    ...   | here = inl (ok , refl)
    ...   | there n = inr n
    Origin : List State → State → Set
    Origin xs y = Σ State λ x → (x ∈ xs) × (Σ Action λ a → Allowed a x × (arrive a x ≡ y))
    origin : ∀ xs {y} → y ∈ expand xs → Origin xs y
    origin (x ∷ xs) m with undo pass x (try refill x (expand xs)) m
    ... | inl (ok , eq) = x , here , pass , ok , eq
    ... | inr n with undo refill x (expand xs) n
    ...   | inl (ok , eq) = x , here , refill , ok , eq
    ...   | inr k with origin xs k
    ...     | v , from , path = v , there from , path

  trace : ∀ legs xs {z} → z ∈ scan legs xs → Σ State λ x → (x ∈ xs) × Run legs x z
  trace [] xs {z} m = z , m , end z
  trace (station s d ∷ legs) xs m with trace legs (Pruning.thinlist (Move.expand s d xs)) m
  ... | y , kept , route with Step.origin s d xs (Thin.subset (Pruning.correct (Move.expand s d xs)) kept)
  ...   | x , old , a , ok , refl = x , old , drive a ok route

  reachable : ∀ legs x {z} → z ∈ scan legs (x ∷ []) → Run legs x z
  reachable legs x m with trace legs (x ∷ []) m
  ... | .x , here , route = route
  ... | _ , there () , _
