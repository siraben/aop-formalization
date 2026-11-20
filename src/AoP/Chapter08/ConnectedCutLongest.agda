{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.ConnectedCutLongest where

open import AoP.Common.Prelude
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter07.LongestPrefix using (module Prefix)
open import AoP.Chapter08.ConnectedBlock using (module Law)
open import AoP.Chapter05.Subsequences using (here; there)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥)

-- Local maximality suffices: any competing prefix either stops
-- inside this block or contains its first rejected extension.
module Cut {A : Set} (Q : A → A → Set) where
  open Prefix {A}
  open Law Q
  boundary : ∀ b a rest {ys} → ys ≼ (b ++ (a ∷ rest)) → (ys ≼ b) ⊎ ((b ++ (a ∷ [])) ≼ ys)
  boundary [] a rest nil = inl nil
  boundary [] a rest (cons p) = inr (cons nil)
  boundary (x ∷ b) a rest nil = inl nil
  boundary (x ∷ b) a rest (cons p) with boundary b a rest p
  ... | inl short = inl (cons short)
  ... | inr long = inr (cons long)
  restrict : ∀ {xs ys} → xs ≼ ys → Connected ys → Connected xs
  restrict p ok a b m n = ok a b (inc p m) (inc p n)
    where open import AoP.Chapter05.Subsequences using (_∈_)
          inc : ∀ {us vs x} → us ≼ vs → x ∈ us → x ∈ vs
          inc (cons _) here = here
          inc (cons q) (there k) = there (inc q k)
  longest : ∀ b a rest → Connected b → (Connected (b ++ (a ∷ [])) → ⊥) → Longest Connected (b ++ (a ∷ rest))
  longest b a rest good reject = result b (a ∷ rest) refl good dominates
    where dominates : ∀ {ys} → ys ≼ (b ++ (a ∷ rest)) → Connected ys → ys ≼ b
          dominates p ok with boundary b a rest p
          ... | inl short = short
          ... | inr long with reject (restrict long ok)
          ...   | ()
