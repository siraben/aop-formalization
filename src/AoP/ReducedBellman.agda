{-# OPTIONS --safe --without-K #-}
module AoP.ReducedBellman where

open import AoP.Prelude
open import AoP.Compression using (module Text)
open import AoP.DictionaryTable using (module Table)
open import AoP.DictionaryBellman using (module Solve)
open import AoP.DictionaryOptimal using (module Certificate)
open import AoP.DictionaryLastEdge using (module Law)
open import AoP.DictionarySplice using (module Splice)
open import AoP.DictionaryTokenCoverage using (module Coverage)
open import AoP.ReducedDictionary using (module Reduced)
open import AoP.ReducedPointerBound using (module Local)
open import AoP.LongestPointerScan using (module Scan)
open import AoP.Naturality using (_++_)
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.NatOrder using (_≤_; chain)
open import AoP.ParagraphMinimum using (Dec)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Maybe using (just)

module Law′ {A : Set} (eq? : (x y : A) → Dec (x ≡ y)) (target : List A) (c p : Nat) where
  open Text {A}
  open Table eq? target c p using (Cell; Row)
  open Solve eq? target c p
  open Splice {A} c p
  open Law {A} using (decompose; earlier)
  open Coverage eq? target using (covered)
  private
    snoc-inj : ∀ (xs ys : List A) a b → xs ++ (a ∷ []) ≡ ys ++ (b ∷ []) → (xs ≡ ys) × (a ≡ b)
    snoc-inj [] [] a .a refl = refl , refl
    snoc-inj [] (_ ∷ []) a b ()
    snoc-inj [] (_ ∷ _ ∷ _) a b ()
    snoc-inj (_ ∷ []) [] a b ()
    snoc-inj (_ ∷ _ ∷ _) [] a b ()
    snoc-inj (x ∷ xs) (y ∷ ys) a b eq with headEq eq | tailEq eq
      where headEq : ∀ {x y : A} {u v} → x ∷ u ≡ y ∷ v → x ≡ y
            headEq refl = refl
            tailEq : ∀ {x y : A} {u v} → x ∷ u ≡ y ∷ v → u ≡ v
            tailEq refl = refl
    ... | refl | q with snoc-inj xs ys a b q
    ... | refl , refl = refl , refl
    last∈ : ∀ (ps : List Code) op → op ∈ ps ++ (op ∷ [])
    last∈ [] op = here
    last∈ (_ ∷ ps) op = there (last∈ ps op)

  module Step (xs : List A) (u : Cell xs) (rs : List Row) (a : A) where
    ys = xs ++ (a ∷ [])
    open Local eq? target c p ys
    open Reduced.Step eq? target c p ys
    open Scan eq? target c p ys using (hit)
    literal : Cell ys
    literal = (fst u ++ (sym a ∷ [])) , resume [] (fst u) (sym a ∷ []) (snd u)
    next = reduce rs literal
    module Proof (rest : List A) (suffix : ys ++ rest ≡ target) (opt : Optimal u)
                 (hist : History rs ys) (all : RowsOptimal rs) where
      rival : ∀ ps state op → run [] ps ≡ just state → run state (op ∷ []) ≡ just ys → price (fst next) ≤ price (ps ++ (op ∷ []))
      rival ps state (sym b) pre step with snoc-inj state xs b a (unj step)
        where unj : ∀ {x y : List A} → just x ≡ just y → x ≡ y
              unj refl = refl
      ... | refl , refl = chain (literal-bound rs literal) (cheaper (fst u) ps (sym a ∷ []) (opt ps pre))
      rival ps state (ptr i k) pre step with hist state (earlier state (ptr i k) step)
      ... | cell , at , _ = pointer-bound rs literal all (hit (state , cell) i k step) at tested ps pre
        where tested = covered (ps ++ (ptr i k ∷ [])) ys rest (resume [] ps (ptr i k ∷ []) pre ∙ step) suffix (last∈ ps (ptr i k))
      optimal : Optimal next
      optimal [] ok = empty-case xs a ok
        where empty-case : ∀ (zs : List A) b {X : Set} → just [] ≡ just (zs ++ (b ∷ [])) → X
              empty-case [] b ()
              empty-case (_ ∷ _) b ()
      optimal (o ∷ os) ok with decompose [] o os ok
      ... | Law.edge ps op state eq pre step rewrite eq = rival ps state op pre step
