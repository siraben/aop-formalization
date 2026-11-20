{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.ReducedDictionaryOptimal where

open import AoP.Common.Prelude
open import AoP.Chapter09.DictionaryTable using (module Table)
open import AoP.Chapter09.DictionaryOptimal using (module Certificate)
open import AoP.Chapter09.DictionaryBellman using (module Solve)
open import AoP.Chapter09.DictionaryHistory using (module Prefix)
open import AoP.Chapter09.ReducedBellman using (module Law′)
open import AoP.Chapter09.ReducedDictionary using (module Reduced)
open import AoP.Chapter09.Compression using (module Text)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Chapter08.ParagraphMinimum using (Dec)
open import AoP.Common.NatOrder using (z≤)
open import Agda.Builtin.Maybe using (just)
open import Agda.Builtin.Nat using (Nat)

module Solver {A : Set} (eq? : (x y : A) → Dec (x ≡ y)) (target : List A) (c p : Nat) where
  open Table eq? target c p using (Cell; Row)
  open Solve eq? target c p using (History; Optimal)
  open Certificate eq? target c p using (advance; transport)
  open Text {A} using (assoc)
  open Prefix {A} using (nonempty)
  open Reduced eq? target c p using (fill; encode)
  All : List Row → Set
  All rs = ∀ r → r ∈ rs → Optimal (snd r)
  push : ∀ {xs rs} (u : Cell xs) → Optimal u → All rs → All ((xs , u) ∷ rs)
  push u opt all _ here = opt
  push u opt all r (there m) = all r m
  invariant : ∀ xs u rs rest → xs ++ rest ≡ target → Optimal u → History rs xs → All rs → Optimal (fill xs u rs rest)
  invariant xs (ps , ok) rs [] split opt hist all qs good = opt qs (good ∙ cong just (unit xs))
    where unit : ∀ (xs : List A) → xs ++ [] ≡ xs
          unit [] = refl
          unit (x ∷ xs) = cong (x ∷_) (unit xs)
  invariant xs u rs (a ∷ rest) split opt hist all = transport eq _ (invariant ys next history rest (eq ∙ split) optimal covered sound)
    where
    history = (xs , u) ∷ rs
    open Law′.Step eq? target c p xs u history a
    eq = assoc xs (a ∷ []) rest
    covered = advance xs u rs a opt hist
    sound = push u opt all
    open Proof rest (eq ∙ split) opt covered sound
  minimum : Optimal encode
  minimum = invariant [] ([] , refl) [] target refl (λ _ _ → z≤) (λ { xs (a , zs , eq) → nonempty xs a zs eq }) (λ r ())
