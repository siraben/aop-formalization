{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.ReducedPointerBound where

open import AoP.Common.Prelude
open import AoP.Chapter09.Compression using (module Text)
open import AoP.Chapter09.DictionaryTable using (module Table)
open import AoP.Chapter09.DictionaryScanBound using (module Bound)
open import AoP.Chapter09.DictionaryBellman using (module Solve)
open import AoP.Chapter09.DictionarySearch using (module Encode)
open import AoP.Chapter09.DictionarySplice using (module Splice)
open import AoP.Chapter09.ReducedDictionary using (module Reduced)
open import AoP.Chapter09.LongestPointerScan using (module Scan)
open import AoP.Chapter09.PointerSpanOrder using (module Order)
open import AoP.Chapter09.LongestPointerDominance using (module Law′)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter05.Subsequences using (_∈_)
open import AoP.Common.NatOrder using (_≤_; rid; chain)
open import AoP.Chapter08.ParagraphMinimum using (Dec)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Maybe using (just)

module Local {A : Set} (eq? : (x y : A) → Dec (x ≡ y)) (target : List A) (c p : Nat) (ys : List A) where
  open Text {A}
  open Table eq? target c p using (Cell; Row)
  open Encode eq? target using (tokens)
  open Splice {A} c p using (price)
  open Scan eq? target c p ys
  open Reduced.Step eq? target c p ys
  open Bound eq? target c p using (both)
  open Solve eq? target c p using (Optimal)
  open Order {A} c p using (starts)
  open Law′ {A} c p using (dominate)
  RowsOptimal : List Row → Set
  RowsOptimal rs = ∀ r → r ∈ rs → Optimal (snd r)
  literal-bound : ∀ rs lit → price (fst (reduce rs lit)) ≤ price (fst lit)
  literal-bound rs lit with longest rs
  ... | none _ = rid _
  ... | won h _ _ = snd (both (program h) lit)

  -- The rival prefix program qs need not be the one stored in its
  -- row. Only the selected longest pointer needs an optimal start row.
  pointer-bound : ∀ rs lit → RowsOptimal rs → ∀ t → Hit.row t ∈ rs → token t ∈ tokens →
    ∀ qs → run [] qs ≡ just (fst (Hit.row t)) → price (fst (reduce rs lit)) ≤ price (qs ++ (token t ∷ []))
  pointer-bound rs lit optimal t member tested qs ok with longest rs
  ... | none no with no t (member , tested)
  ...   | ()
  pointer-bound rs lit optimal t member tested qs ok | won h (inRows , _) maximum =
    chain (fst (both (program h) lit)) (snd (dominate path (fst (snd (Hit.row h))) qs
      (Hit.offset h) (Hit.span h) (Hit.offset t) (Hit.span t) (snd (snd (Hit.row h)))
      (optimal (Hit.row h) inRows) ok (Hit.legal h) (Hit.legal t)))
    where
    path = starts (fst (Hit.row h)) (fst (Hit.row t)) (Hit.offset h) (Hit.offset t)
      (Hit.span h) (Hit.span t) (Hit.legal h) (Hit.legal t) (maximum t (member , tested))
