{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.ReducedDictionary where

open import AoP.Common.Prelude
open import AoP.Chapter09.Compression using (module Text)
open import AoP.Chapter09.DictionaryTable using (module Table)
open import AoP.Chapter09.DictionarySplice using (module Splice)
open import AoP.Chapter09.LongestPointerScan using (module Scan)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter08.ParagraphMinimum using (Dec)
open import Agda.Builtin.Nat using (Nat)

-- §9.4. Per nonempty prefix compare the literal extension with at
-- most one pointer program. Finding that pointer still scans the rows
-- and the bounded tokens; the reduction is in the cost comparison.
module Reduced {A : Set} (eq? : (x y : A) → Dec (x ≡ y)) (target : List A) (c p : Nat) where
  open Text {A}
  open Table eq? target c p using (Cell; Row; choose; substCell)
  open Splice {A} c p using (resume)
  module Step (ys : List A) where
    open Scan eq? target c p ys
    program : Hit → Cell ys
    program (hit (xs , ps , ok) i k legal) = (ps ++ (ptr i k ∷ [])) , (resume [] ps (ptr i k ∷ []) ok ∙ legal)
    reduce : List Row → Cell ys → Cell ys
    reduce rs literal with longest rs
    ... | none _ = literal
    ... | won h _ _ = choose (program h) literal
  fill : ∀ xs → Cell xs → List Row → (rest : List A) → Cell (xs ++ rest)
  fill xs (ps , ok) rs [] = ps , (ok ∙ prefix-law xs [])
  fill xs u rs (a ∷ rest) = substCell (assoc xs (a ∷ []) rest) (fill ys next hist rest)
    where
    ys = xs ++ (a ∷ [])
    hist = (xs , u) ∷ rs
    literal : Cell ys
    literal = (fst u ++ (sym a ∷ [])) , resume [] (fst u) (sym a ∷ []) (snd u)
    next = Step.reduce ys hist literal
  encode : Cell target
  encode = fill [] ([] , refl) [] target
