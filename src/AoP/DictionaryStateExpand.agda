{-# OPTIONS --safe --without-K #-}
module AoP.DictionaryStateExpand where

open import AoP.Prelude
open import AoP.Compression using (module Text)
open import AoP.CompressionGrowth using (len)
open import AoP.BoundedWords using (indices)
open import AoP.DictionarySearch using (module Encode)
open import AoP.DictionaryThinState using (module State)
open import AoP.DictionaryStatePrune using (module Pool)
open import AoP.ParagraphMinimum using (Dec)
open import AoP.Polynomial using (inl; inr)
open import AoP.Naturality using (_++_)
open import AoP.DictionarySplice using (module Splice)
open import AoP.Snoc using (Snoc; ε; _▻_)
open import AoP.DictionaryConverseFold using (module Inverse)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Maybe using (just; nothing)

module Fold {A : Set} (eq? : (x y : A) → Dec (x ≡ y)) (c p : Nat) where
  open Text {A}
  open State {A} c p
  open Pool eq? c p using (Candidate; module At)
  open Encode eq? [] using (list?)
  open Splice {A} c p using (resume)
  open Inverse {A} using (text)
  copies? : ∀ xs i n ys → Dec (copy i n xs ≡ just ys)
  copies? xs i n ys with copy i n xs
  ... | nothing = inr (λ ())
  ... | just zs with list? zs ys
  ...   | inl refl = inl refl
  ...   | inr no = inr λ { refl → no refl }
  module Next (ys : List A) (a : A) where
    zs = ys ++ (a ∷ [])
    Child : ∀ {j} → Entry ys j → Set
    Child u = Σ (Candidate zs) λ w → Move a u (snd w)
    start-at : ∀ {j} (u : Entry ys j) → Nat → List (Child u)
    start-at u i with copies? ys i 1 zs
    ... | inl ok = (_ , start u i ok) ∷ []
    ... | inr _ = []
    starts : ∀ {j} (u : Entry ys j) → List Nat → List (Child u)
    starts u [] = []
    starts u (i ∷ is) = start-at u i ++ starts u is
    growth : ∀ {j} (u : Entry ys j) → List (Child u)
    growth (plain _ _) = []
    growth (copying xs i k ps pre cp) with copies? xs i (suc (suc k)) zs
    ... | inl ok = (_ , grow ok) ∷ []
    ... | inr _ = []
    successors : ∀ {j} (u : Entry ys j) → List (Child u)
    successors u = (_ , emit u) ∷ (starts u (indices (len ys)) ++ growth u)
    entries : ∀ {j} {u : Entry ys j} → List (Child u) → List (Candidate zs)
    entries [] = []
    entries (w ∷ ws) = fst w ∷ entries ws
    expand : List (Candidate ys) → List (Candidate zs)
    expand [] = []
    expand ((_ , u) ∷ us) = entries (successors u) ++ expand us
  table : ∀ t → List (Candidate (text t))
  table ε = (closed , plain [] refl) ∷ []
  table (t ▻ a) = fst (At.prune _ (Next.expand (text t) a (table t)))
