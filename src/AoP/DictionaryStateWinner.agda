{-# OPTIONS --safe --without-K #-}
module AoP.DictionaryStateWinner where

open import AoP.Prelude
open import AoP.Snoc using (Snoc; ε; _▻_)
open import AoP.DictionaryStateRuns using (module Runs)
open import AoP.DictionaryThinState using (module State)
open import AoP.DictionaryStatePrune using (module Pool)
open import AoP.DictionaryStateExpand using (module Fold)
open import AoP.DictionaryConverseFold using (module Inverse)
open import AoP.DictionarySplice using (module Splice)
open import AoP.Compression using (module Text)
open import AoP.FiniteMinimum using (module Search)
open import AoP.Polynomial using (inl)
open import AoP.ParagraphMinimum using (Dec)
open import AoP.Complement using (⊥)
open import AoP.NatOrder using (_≤_; chain)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Maybe using (just)

module Winner {A : Set} (eq? : (x y : A) → Dec (x ≡ y)) (c p : Nat) where
  open Runs eq? c p
  open State {A} c p
  open Fold eq? c p using (table)
  open Pool eq? c p using (Candidate)
  open Inverse {A} using (text)
  open Splice {A} c p using (price)
  open Text {A} using (Code; run)
  literal-path : ∀ t → Σ (Candidate (text t)) (Run t)
  literal-path ε = _ , start-run
  literal-path (t ▻ a) with literal-path t
  ... | (_ , u) , path = _ , step path (emit u)
  module At (t : Snoc A) where
    cost : Candidate (text t) → Nat
    cost w = price (program (snd w))
    open Search (λ (_ : Candidate (text t)) → 0 ≡ 0) (λ _ → inl refl) cost
    Answer = Σ (List Code) λ ps → (run [] ps ≡ just (text t)) × (∀ w → Run t w → price ps ≤ cost w)
    solve : Answer
    solve with scan (table t)
    ... | none no with literal-path t
    ...   | w , path with coverage path
    ...     | v , member , _ with no v member refl
    ...       | ()
    solve | best u member _ least = program (snd u) , valid (snd u) , bound
      where bound : ∀ w → Run t w → cost u ≤ cost w
            bound (j , w) path with coverage path
            ... | (.j , v) , at , refl , le = chain (least _ at refl) (ordered v w le)
