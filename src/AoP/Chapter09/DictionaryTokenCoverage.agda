{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.DictionaryTokenCoverage where

open import AoP.Common.Prelude
open import AoP.Chapter09.DictionarySearch using (module Encode)
open import AoP.Chapter09.DictionarySplice using (module Splice)
open import AoP.Chapter09.Compression using (module Text)
open import AoP.Chapter09.CompressionAlphabet using (module Letters)
open import AoP.Chapter09.PointerBounds using (module Bounds)
open import AoP.Chapter09.BoundedWords using (module Words)
open import AoP.Chapter08.ParagraphMinimum using (Dec)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import Agda.Builtin.Maybe using (just)

-- The table enumerates tokens for the *whole* target. To show that
-- these cover any intermediate prefix program, complete the decoder
-- run with literals for the remaining text and reuse its token bounds.
module Coverage {A : Set} (eq? : (x y : A) → Dec (x ≡ y)) (target : List A) where
  open Text {A}
  open Encode eq? target using (over; tokens)
  open Words tokens using (Over; extend)
  open Letters {A} using (alphabet)
  open Bounds {A} using (all-bounded)
  open Splice {A} 0 0 using (resume)

  in-prefix : ∀ ps qs {op} → op ∈ ps → Over (ps ++ qs) → op ∈ tokens
  in-prefix (_ ∷ ps) qs here (extend t ts) = t
  in-prefix (_ ∷ ps) qs (there m) (extend t ts) = in-prefix ps qs m ts

  covered : ∀ ps xs rest {op} → run [] ps ≡ just xs → xs ++ rest ≡ target → op ∈ ps → op ∈ tokens
  covered ps xs rest ok split m = in-prefix ps suffix m (over (alphabet full [] good) (all-bounded full [] good))
    where
    suffix = literals rest
    full = ps ++ suffix
    good : run [] full ≡ just target
    good = resume [] ps suffix ok ∙ prefix-law xs rest ∙ cong just split
