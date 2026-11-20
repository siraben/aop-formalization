{-# OPTIONS --safe --without-K #-}
module AoP.DictionaryStateRuns where

open import AoP.Prelude
open import AoP.Snoc using (Snoc; ε; _▻_)
open import AoP.DictionaryThinState using (module State)
open import AoP.DictionaryConverseFold using (module Inverse)
open import AoP.DictionaryStateExpand using (module Fold)
open import AoP.DictionaryMoveCoverage using (module Cover)
open import AoP.DictionaryStatePrune using (module Pool)
open import AoP.Subsequences using (_∈_; here; there; merge)
open import AoP.Naturality using (_++_)
open import AoP.ParagraphMinimum using (Dec)
open import AoP.NatOrder using (rid; chain)
open import AoP.Polynomial using (inl; inr)
open import AoP.Thinning using (Thin)
open import Agda.Builtin.Nat using (Nat)

-- Global coverage of all legal state runs by the computed frontier.
module Runs {A : Set} (eq? : (x y : A) → Dec (x ≡ y)) (c p : Nat) where
  open State {A} c p
  open Pool eq? c p using (Candidate; Beats; module At)
  open Fold eq? c p using (table; module Next)
  open Inverse {A} using (text)
  data Run : (t : Snoc A) → Candidate (text t) → Set where
    start-run : Run ε (closed , plain [] refl)
    step : ∀ {t j k a} {v : Entry (text t) j} {w : Entry (text (t ▻ a)) k} → Run t (j , v) → Move a v w → Run (t ▻ a) (k , w)
  Rep : ∀ {ys} → List (Candidate ys) → Candidate ys → Set
  Rep xs w = Σ _ λ v → (v ∈ xs) × Beats v w
  module Layer (ys : List A) (a : A) where
    open Next ys a
    member : ∀ {j} {u : Entry ys j} (cs : List (Child u)) {e} → e ∈ cs → fst e ∈ entries cs
    member (_ ∷ _) here = here
    member (_ ∷ cs) (there m) = there (member cs m)
    collect : ∀ {j} {u : Entry ys j} rs → (j , u) ∈ rs → ∀ {e} → e ∈ successors u → fst e ∈ expand rs
    collect ((_ , u) ∷ rs) here m = merge (entries (successors u)) (expand rs) (inl (member (successors u) m))
    collect ((_ , v) ∷ rs) (there at) m = merge (entries (successors v)) (expand rs) (inr (collect rs at m))
    next : ∀ rs {j k} {v : Entry ys j} {w : Entry zs k} → Rep rs (j , v) → Move a v w → Rep (fst (At.prune zs (expand rs))) (k , w)
    next rs ((. _ , u) , at , refl , le) mv with match {u = u} le mv
    ... | z , replay , cheap with Cover.covers eq? c p ys a replay
    ... | child , in-list , refl , bound with Thin.cover (snd (At.prune zs (expand rs))) (fst child) (collect rs at in-list)
    ... | kept , in-pool , key , less = kept , in-pool , key , chain less (chain bound cheap)
  coverage : ∀ {t w} → Run t w → Rep (table t) w
  coverage start-run = _ , here , refl , rid _
  coverage (step {t} {a = a} path mv) = Layer.next (text t) a (table t) (coverage path) mv
