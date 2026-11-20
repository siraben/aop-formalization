{-# OPTIONS --safe --without-K #-}
module AoP.DictionaryOptimal where

open import AoP.Prelude
open import AoP.Compression using (module Text)
open import AoP.DictionaryBellman using (module Solve)
open import AoP.DictionaryHistory using (module Prefix)
open import AoP.DictionaryTable using (module Table)
open import AoP.DictionarySplice using (module Splice)
open import AoP.Subsequences using (here; there)
open import AoP.Polynomial using (inl; inr)
open import AoP.ParagraphMinimum using (Dec)
open import AoP.Naturality using (_++_)
open import AoP.NatOrder using (z≤)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat)

module Certificate {A : Set} (eq? : (x y : A) → Dec (x ≡ y)) (target : List A) (c p : Nat) where
  open Text {A}
  open Solve eq? target c p
  open Table eq? target c p
  open Prefix {A}
  open Splice {A} c p using (resume)
  advance : ∀ xs u rs a → Optimal u → History rs xs → History ((xs , u) ∷ rs) (xs ++ (a ∷ []))
  advance xs u rs a opt hist ys sub with previous ys xs a sub
  ... | inl refl = u , here , opt
  ... | inr prev = let v , at , ok = hist ys prev in v , there at , ok
  row-best : ∀ xs a rest rs fallback → (xs ++ (a ∷ [])) ++ rest ≡ target → History rs (xs ++ (a ∷ [])) → Optimal (rows (xs ++ (a ∷ [])) rs fallback)
  row-best [] a = best a []
  row-best (b ∷ xs) a = best b (xs ++ (a ∷ []))
  transport : ∀ {xs ys} (eq : xs ≡ ys) u → Optimal u → Optimal (substCell eq u)
  transport refl u opt = opt
  private
    unit : ∀ (xs : List A) → xs ++ [] ≡ xs
    unit [] = refl
    unit (x ∷ xs) = cong (x ∷_) (unit xs)
  invariant : ∀ xs u rs rest → xs ++ rest ≡ target → Optimal u → History rs xs → Optimal (fill xs u rs rest)
  invariant xs (ps , ok) rs [] split opt hist qs good = opt qs (good ∙ cong just (unit xs))
  invariant xs u rs (a ∷ rest) split opt hist = transport eq _ (invariant ys next history rest (eq ∙ split) optimal covered)
    where
    ys = xs ++ (a ∷ [])
    eq = assoc xs (a ∷ []) rest
    history = (xs , u) ∷ rs
    covered = advance xs u rs a opt hist
    fallback : Cell ys
    fallback = (fst u ++ (sym a ∷ [])) , resume [] (fst u) (sym a ∷ []) (snd u)
    next = rows ys history fallback
    optimal = row-best xs a rest history fallback (eq ∙ split) covered
  minimum : Optimal encode
  minimum = invariant [] ([] , refl) [] target refl (λ _ _ → z≤) (λ { xs (a , zs , eq) → nonempty xs a zs eq })
