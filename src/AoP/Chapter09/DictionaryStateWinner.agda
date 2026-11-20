{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.DictionaryStateWinner where

open import AoP.Common.Prelude
open import AoP.Chapter01.Snoc using (Snoc; ε; _▻_)
open import AoP.Chapter09.DictionaryStateRuns using (module Runs)
open import AoP.Chapter09.DictionaryThinState using (module State)
open import AoP.Chapter09.DictionaryStatePrune using (module Pool)
open import AoP.Chapter09.DictionaryStateExpand using (module Fold)
open import AoP.Chapter09.DictionaryConverseFold using (module Inverse)
open import AoP.Chapter09.DictionarySplice using (module Splice)
open import AoP.Chapter09.Compression using (module Text)
open import AoP.Common.FiniteMinimum using (module Search)
open import AoP.Chapter02.Polynomial using (inl)
open import AoP.Chapter08.ParagraphMinimum using (Dec)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Common.NatOrder using (_≤_; chain)
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
