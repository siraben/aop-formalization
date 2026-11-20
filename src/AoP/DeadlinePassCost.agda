{-# OPTIONS --safe --without-K #-}
module AoP.DeadlinePassCost where

open import AoP.Prelude
open import AoP.DeadlineMergeRound
open import AoP.Tardiness using (Job)
open import AoP.Naturality using (_++_)
open import AoP.ConversionCost using (len)
open import AoP.Permutations using (Perm; Insert; front; later; empty; insert)
open import AoP.NatOrder using (_≤_; z≤; sum-mono)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open Pass

-- The one-pass bound is stated in terms of output jobs. Convert it to
-- an input bound using occurrence preservation, before summing passes.
private
  back : ∀ {x y : Nat} → x ≡ y → y ≡ x
  back refl = refl
  append-size : ∀ (xs ys : List Job) → len (xs ++ ys) ≡ len xs + len ys
  append-size [] ys = refl
  append-size (x ∷ xs) ys = cong suc (append-size xs ys)
  flat-size : ∀ rs → len (flat rs) ≡ mass rs
  flat-size [] = refl
  flat-size (x ∷ xs) = append-size x (flat xs) ∙ cong (len x +_) (flat-size xs)
  grows : ∀ {x : Job} {ys zs} → Insert x ys zs → suc (len ys) ≡ len zs
  grows front = refl
  grows (later i) = cong suc (grows i)
  size : ∀ {xs ys : List Job} → Perm xs ys → len xs ≡ len ys
  size empty = refl
  size (insert p i) = cong suc (size p) ∙ grows i

conserved : ∀ rs → mass (out (round rs)) ≡ mass rs
conserved rs = back (flat-size (out (round rs))) ∙ back (size (perm (round rs))) ∙ flat-size rs

work : Nat → Runs → Nat
work 0 rs = 0
work (suc k) rs = comparisons (round rs) + work k (out (round rs))

bound : ∀ k rs → work k rs ≤ k * mass rs
bound 0 rs = z≤
bound (suc k) rs with cost-bound (round rs) | bound k (out (round rs))
... | pass-le | rest-le rewrite conserved rs = sum-mono pass-le rest-le
