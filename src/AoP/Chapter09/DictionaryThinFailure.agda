{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.DictionaryThinFailure where

open import AoP.Common.Prelude
open import AoP.Chapter09.DictionaryTableTrace using (Letter; a)
open import AoP.Chapter09.Compression using (module Text)
open import AoP.Chapter09.DictionaryConverseStep using (module Step)
open import AoP.Chapter09.DictionarySplice using (module Splice)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Common.NatOrder using (_≤_; rid; weaken)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 9.20: at aa, pruning by price alone can discard an open
-- pointer. Its extra letter at aaa would have been free.
open Text {Letter}
open Step {Letter}
open Splice {Letter} 2 3
cheap open-copy grown : List Code
cheap = sym a ∷ sym a ∷ []
open-copy = sym a ∷ ptr 0 0 ∷ []
grown = sym a ∷ ptr 0 1 ∷ []
cheap-ok : run [] cheap ≡ just (a ∷ a ∷ [])
cheap-ok = refl
copy-ok : run [] open-copy ≡ just (a ∷ a ∷ [])
copy-ok = refl
switch : Extend a open-copy grown
switch = grow-ptr (sym a ∷ []) 0 0 (a ∷ []) (a ∷ a ∷ []) refl refl refl
prices : (price cheap ≡ 4) × ((price open-copy ≡ 5) × (price grown ≡ 5))
prices = refl , refl , refl

bound : ∀ {ps qs} → Extend a ps qs → ps ≡ cheap → 6 ≤ price qs
bound (literal .cheap) refl = rid 6
bound (begin-ptr .cheap i xs ok found) refl = weaken (rid 6)
bound (grow-ptr [] i k xs ys pre sh lo) ()
bound (grow-ptr (_ ∷ []) i k xs ys pre sh lo) ()
bound (grow-ptr (_ ∷ _ ∷ []) i k xs ys pre sh lo) ()
bound (grow-ptr (_ ∷ _ ∷ _ ∷ _) i k xs ys pre sh lo) ()
