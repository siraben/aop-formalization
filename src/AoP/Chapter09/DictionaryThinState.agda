{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.DictionaryThinState where

open import AoP.Common.Prelude
open import AoP.Chapter09.Compression using (module Text)
open import AoP.Chapter09.DictionarySplice using (module Splice)
open import AoP.Chapter09.DictionaryConverseStep using (module Step)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Common.NatOrder using (_≤_; rid; sum-mono)
open import Agda.Builtin.Nat using (Nat; suc; _+_)
open import Agda.Builtin.Maybe using (just)

-- 9.20: distinguish codes that can still lengthen their last pointer.
-- A pointer state saves the preceding text, offset and span. For a
-- fixed key only the price of the encoding *before* the pointer varies.
module State {A : Set} (c p : Nat) where
  open Text {A}
  open Splice {A} c p
  open Step {A} using (Extend; literal; begin-ptr; grow-ptr)
  data Key : Set where
    closed : Key
    active : List A → Nat → Nat → Key
  data Entry (ys : List A) : Key → Set where
    plain : ∀ ps → run [] ps ≡ just ys → Entry ys closed
    copying : ∀ xs i k ps → run [] ps ≡ just xs → copy i (suc k) xs ≡ just ys → Entry ys (active xs i k)
  program : ∀ {ys key} → Entry ys key → List Code
  program (plain ps _) = ps
  program (copying xs i k ps _ _) = ps ++ (ptr i k ∷ [])
  base : ∀ {ys key} → Entry ys key → Nat
  base (plain ps _) = price ps
  base (copying xs i k ps _ _) = price ps
  ordered : ∀ {ys key} (u v : Entry ys key) → base u ≤ base v → price (program u) ≤ price (program v)
  ordered (plain ps _) (plain qs _) le = le
  ordered (copying xs i k ps _ _) (copying .xs .i .k qs _ _) le rewrite append-cost ps (ptr i k ∷ []) | append-cost qs (ptr i k ∷ []) = sum-mono le (rid _)
  valid : ∀ {ys key} (u : Entry ys key) → run [] (program u) ≡ just ys
  valid (plain ps ok) = ok
  valid (copying xs i k ps ok cp) = resume [] ps _ ok ∙ go cp
    where go : ∀ {ys} → copy i (suc k) xs ≡ just ys → run xs (ptr i k ∷ []) ≡ just ys
          go eq rewrite eq = refl
  data Move {ys : List A} (a : A) : ∀ {j k} → Entry ys j → Entry (ys ++ (a ∷ [])) k → Set where
    emit : ∀ {j} (u : Entry ys j) → Move a u (plain (program u ++ (sym a ∷ [])) (resume [] (program u) _ (valid u)))
    start : ∀ {j} (u : Entry ys j) i (ok : copy i 1 ys ≡ just (ys ++ (a ∷ []))) → Move a u (copying ys i 0 (program u) (valid u) ok)
    grow : ∀ {xs i k ps pre cp} (ok : copy i (suc (suc k)) xs ≡ just (ys ++ (a ∷ []))) → Move a (copying xs i k ps pre cp) (copying xs i (suc k) ps pre ok)
  match : ∀ {ys a j k} {u v : Entry ys j} {w : Entry (ys ++ (a ∷ [])) k} → base u ≤ base v → Move a v w → Σ (Entry _ k) λ z → Move a u z × (base z ≤ base w)
  match {a = a} {u = u} le (emit v) = _ , emit u , cheaper (program u) (program v) (sym a ∷ []) (ordered u v le)
  match {u = u} le (start v i ok) = _ , start u i ok , ordered u v le
  match {u = copying xs i k ps pre cp} le (grow ok) = _ , grow ok , le
