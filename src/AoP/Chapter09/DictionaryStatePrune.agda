{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.DictionaryStatePrune where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; rid)
open import AoP.Chapter08.ParagraphMinimum using (Dec; le?)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Chapter09.DictionaryThinState using (module State)
open import AoP.Chapter09.DictionarySearch using (module Encode)
open import AoP.Chapter09.PoolPruning using (module Sweep)
open import AoP.Chapter01.Naturality using (_++_)
open import Agda.Builtin.Nat using (Nat; suc)

-- Retain a subset of a finite candidate list, with a same-key,
-- no-more-expensive representative for each discarded candidate.
module Pool {A : Set} (eq? : (x y : A) → Dec (x ≡ y)) (c p : Nat) where
  open State {A} c p
  open Encode eq? [] using (list?)
  nat? : ∀ (i j : Nat) → Dec (i ≡ j)
  nat? 0 0 = inl refl
  nat? 0 (suc j) = inr (λ ())
  nat? (suc i) 0 = inr (λ ())
  nat? (suc i) (suc j) with nat? i j
  ... | inl refl = inl refl
  ... | inr no = inr λ { refl → no refl }
  key? : ∀ (i j : Key) → Dec (i ≡ j)
  key? closed closed = inl refl
  key? closed (active _ _ _) = inr (λ ())
  key? (active _ _ _) closed = inr (λ ())
  key? (active xs i k) (active ys j n) with list? xs ys | nat? i j | nat? k n
  ... | inl refl | inl refl | inl refl = inl refl
  ... | inr no | _ | _ = inr λ { refl → no refl }
  ... | _ | inr no | _ = inr λ { refl → no refl }
  ... | _ | _ | inr no = inr λ { refl → no refl }
  Candidate : List A → Set
  Candidate ys = Σ Key (Entry ys)
  Beats : ∀ {ys} → Candidate ys → Candidate ys → Set
  Beats (j , u) (k , v) = (j ≡ k) × (base u ≤ base v)
  test : ∀ {ys} (u v : Candidate ys) → Dec (Beats u v)
  test (j , u) (k , v) with key? j k | le? (base u) (base v)
  ... | inl eq | inl le = inl (eq , le)
  ... | inr no | _ = inr λ z → no (fst z)
  ... | _ | inr no = inr λ z → no (snd z)
  module At (ys : List A) where
    open Sweep (Beats {ys}) (λ u → refl , rid _) test public using (prune)
