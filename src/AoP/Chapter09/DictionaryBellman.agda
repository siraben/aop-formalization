{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.DictionaryBellman where

open import AoP.Common.Prelude
open import AoP.Chapter09.Compression using (module Text)
open import AoP.Chapter09.DictionaryTable using (module Table)
open import AoP.Chapter09.DictionaryScanBound using (module Bound)
open import AoP.Chapter09.DictionarySplice using (module Splice)
open import AoP.Chapter09.DictionaryLastEdge using (module Law)
open import AoP.Chapter09.DictionaryHistory using (module Prefix)
open import AoP.Chapter09.DictionaryTokenCoverage using (module Coverage)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Common.NatOrder using (_≤_; chain)
open import AoP.Chapter08.ParagraphMinimum using (Dec)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Maybe using (just)

module Solve {A : Set} (eq? : (x y : A) → Dec (x ≡ y)) (target : List A) (c p : Nat) where
  open Text {A}
  open Table eq? target c p
  open Bound eq? target c p using (edge)
  open Coverage eq? target using (covered)
  open Splice {A} c p using (price; cheaper)
  open Law {A} using (Last; decompose; earlier)
  open Prefix {A} using (Proper)
  Optimal : ∀ {xs} → Cell xs → Set
  Optimal {xs} u = ∀ ps → run [] ps ≡ just xs → price (fst u) ≤ price ps
  History : List Row → List A → Set
  History rs ys = ∀ xs → Proper xs ys → Σ (Cell xs) λ u → ((xs , u) ∈ rs) × Optimal u
  private
    last∈ : ∀ (ps : List Code) op → op ∈ ps ++ (op ∷ [])
    last∈ [] op = here
    last∈ (x ∷ ps) op = there (last∈ ps op)
  -- A nonempty prefix has a nonempty rival program. Factor it at the
  -- last instruction, recover an optimal row, and append that same
  -- instruction to the row before comparing with the scanner's winner.
  best : ∀ a xs rest rs fallback → (a ∷ xs) ++ rest ≡ target → History rs (a ∷ xs) → Optimal (rows (a ∷ xs) rs fallback)
  best a xs rest rs fallback split hist [] ()
  best a xs rest rs fallback split hist (o ∷ os) ok with decompose [] o os ok
  ... | Law.edge ps op state eq pre step with hist state (earlier state op step)
  ... | u , member , opt = compare-program eq
    where
    tok = covered (o ∷ os) (a ∷ xs) rest ok split (substMem eq (last∈ ps op))
      where substMem : ∀ {xs ys : List Code} {o} → xs ≡ ys → o ∈ ys → o ∈ xs
            substMem refl m = m
    local = edge (a ∷ xs) rs fallback (state , u) op member tok step
    compare-program : ∀ {qs} → qs ≡ ps ++ (op ∷ []) → price (fst (rows (a ∷ xs) rs fallback)) ≤ price qs
    compare-program refl = chain local (cheaper (fst u) ps (op ∷ []) (opt ps pre))
