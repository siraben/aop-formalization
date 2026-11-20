{-# OPTIONS --safe --without-K #-}
module AoP.DictionaryConverseStep where

open import AoP.Prelude
open import AoP.Compression using (module Text)
open import AoP.DictionaryLastEdge using (module Law)
open import AoP.DictionarySplice using (module Splice)
open import AoP.ShortenPointer using () renaming (module Law to Short)
open import AoP.Naturality using (_++_)
open import Agda.Builtin.Maybe using (just; nothing)
open import Agda.Builtin.Nat using (suc)

-- One letter of inverse decoding either begins a literal, begins a
-- one-letter pointer, or lengthens the last pointer of an encoding.
module Step {A : Set} where
  open Text {A}
  open Splice {A} 0 0 using (resume)
  data Extend (a : A) : List Code → List Code → Set where
    literal : ∀ ps → Extend a ps (ps ++ (sym a ∷ []))
    begin-ptr : ∀ ps i xs → run [] ps ≡ just xs → lookup i xs ≡ just a → Extend a ps (ps ++ (ptr i 0 ∷ []))
    grow-ptr : ∀ ps i k xs ys → run [] ps ≡ just xs → copy i (suc k) xs ≡ just ys →
      copy i (suc (suc k)) xs ≡ just (ys ++ (a ∷ [])) → Extend a (ps ++ (ptr i k ∷ [])) (ps ++ (ptr i (suc k) ∷ []))

  private
    copy-run : ∀ xs i k {ys} → copy i (suc k) xs ≡ just ys → run xs (ptr i k ∷ []) ≡ just ys
    copy-run xs i k eq rewrite eq = refl
    inject : ∀ {xs ys : List A} → just xs ≡ just ys → xs ≡ ys
    inject refl = refl
    rev : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
    rev refl = refl
  sound : ∀ {a ps qs xs} → Extend a ps qs → run [] ps ≡ just xs → run [] qs ≡ just (xs ++ (a ∷ []))
  sound (literal ps) ok = resume [] ps _ ok
  sound (begin-ptr ps i xs pre found) ok with inject (rev pre ∙ ok)
  ... | refl = resume [] ps _ pre ∙ copy-run xs i 0 (one xs found)
    where one : ∀ xs {a} → lookup i xs ≡ just a → copy i 1 xs ≡ just (xs ++ (a ∷ []))
          one xs eq rewrite eq = refl
  sound (grow-ptr ps i k xs ys pre short long) ok with inject (rev (resume [] ps _ pre ∙ copy-run xs i k short) ∙ ok)
  ... | refl = resume [] ps _ pre ∙ copy-run xs i (suc k) long
