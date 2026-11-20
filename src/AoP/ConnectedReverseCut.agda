{-# OPTIONS --safe --without-K #-}
module AoP.ConnectedReverseCut where

open import AoP.Prelude
open import AoP.Naturality using (_++_)
open import AoP.Subsequences using (_∈_; here; there; merge; split)
open import AoP.Polynomial using (inl; inr)
open import AoP.ConnectedBlock using (module Law)
open import AoP.ConnectedCutLongest using (module Cut)
open import AoP.LongestPrefix using (module Prefix)
open import AoP.Complement using (⊥)

-- Restore input order at the instant a streaming block closes. Both
-- connectedness and failure of the next extension depend solely on
-- membership, so each certificate transports through reversal.
module Restore {A : Set} (Q : A → A → Set) where
  open Law Q
  open Prefix {A}
  rev : List A → List A
  rev [] = []
  rev (x ∷ xs) = rev xs ++ (x ∷ [])
  forward : ∀ xs {a} → a ∈ xs → a ∈ rev xs
  forward (x ∷ xs) here = merge (rev xs) (x ∷ []) (inr here)
  forward (x ∷ xs) (there m) = merge (rev xs) (x ∷ []) (inl (forward xs m))
  backward : ∀ xs {a} → a ∈ rev xs → a ∈ xs
  backward [] ()
  backward (x ∷ xs) m with split (rev xs) (x ∷ []) m
  ... | inl h = there (backward xs h)
  ... | inr here = here
  ... | inr (there ())
  cut : ∀ xs a rest → Connected xs → (Connected (a ∷ xs) → ⊥) → Longest Connected (rev xs ++ (a ∷ rest))
  cut xs a rest ok fail = Cut.longest Q (rev xs) a rest good reject
    where good : Connected (rev xs)
          good x y p q = ok x y (backward xs p) (backward xs q)
          reject : Connected (rev (a ∷ xs)) → ⊥
          reject c = fail (λ x y p q → c x y (forward (a ∷ xs) p) (forward (a ∷ xs) q))
