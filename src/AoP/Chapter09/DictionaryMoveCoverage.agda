{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.DictionaryMoveCoverage where

open import AoP.Common.Prelude
open import AoP.Chapter09.DictionaryThinState using (module State)
open import AoP.Chapter09.DictionaryStateExpand using (module Fold)
open import AoP.Chapter09.DictionaryStatePrune using (module Pool)
open import AoP.Chapter09.PointerBounds using (module Bounds)
open import AoP.Chapter09.CompressionGrowth using (len)
open import AoP.Chapter09.BoundedWords using (indices; index-member)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter05.Subsequences using (_∈_; here; there; merge)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Chapter08.ParagraphMinimum using (Dec)
open import AoP.Common.NatOrder using (rid)
open import Agda.Builtin.Nat using (Nat; suc)

-- The decision procedures used by the enumerator may produce different
-- validity proofs from the rival. Compare keys and costs instead of
-- identifying equality witnesses.
module Cover {A : Set} (eq? : (x y : A) → Dec (x ≡ y)) (c p : Nat) (ys : List A) (a : A) where
  open State {A} c p
  open Pool eq? c p using (Candidate; Beats)
  open Fold eq? c p using (copies?; module Next)
  open Next ys a
  Covered : ∀ {j} {u : Entry ys j} → List (Child u) → Candidate zs → Set
  Covered {u = u} cs w = Σ (Child u) λ e → (e ∈ cs) × Beats (fst e) w
  left : ∀ {j} {u : Entry ys j} (xs xs′ : List (Child u)) {w} → Covered xs w → Covered (xs ++ xs′) w
  left xs xs′ (e , m , b) = e , merge xs xs′ (inl m) , b
  right : ∀ {j} {u : Entry ys j} (xs xs′ : List (Child u)) {w} → Covered xs′ w → Covered (xs ++ xs′) w
  right xs xs′ (e , m , b) = e , merge xs xs′ (inr m) , b
  at-index : ∀ {j} (u : Entry ys j) i ok → Covered (start-at u i) (_ , copying ys i 0 (program u) (valid u) ok)
  at-index u i ok with copies? ys i 1 zs
  ... | inl dec = _ , here , refl , rid _
  ... | inr no with no ok
  ...   | ()
  among : ∀ {j} (u : Entry ys j) i is ok → i ∈ is → Covered (starts u is) (_ , copying ys i 0 (program u) (valid u) ok)
  among u i (.i ∷ is) ok here = left (start-at u i) (starts u is) {w = _ , copying ys i 0 (program u) (valid u) ok} (at-index u i ok)
  among u i (n ∷ is) ok (there m) = right (start-at u n) (starts u is) {w = _ , copying ys i 0 (program u) (valid u) ok} (among u i is ok m)
  tail : ∀ {j} {u : Entry ys j} {w} → Covered (starts u (indices (len ys)) ++ growth u) w → Covered (successors u) w
  tail (e , m , b) = e , there m , b
  covers : ∀ {j k} {u : Entry ys j} {w : Entry zs k} → Move a u w → Covered (successors u) (k , w)
  covers (emit u) = _ , here , refl , rid _
  covers (start u i ok) = tail {u = u} {w = w} (left (starts u ns) (growth u) {w = w} (among u i ns ok member))
    where w : Candidate zs
          w = _ , copying ys i 0 (program u) (valid u) ok
          ns = indices (len ys)
          member = index-member i (len ys) (Bounds.first-lookup i 0 ys ok)
  covers {u = u@(copying xs i k ps pre cp)} (grow ok) with copies? xs i (suc (suc k)) zs
  ... | inl dec = _ , there (merge (starts u (indices (len ys))) _ (inr here)) , refl , rid _
  ... | inr no with no ok
  ...   | ()
