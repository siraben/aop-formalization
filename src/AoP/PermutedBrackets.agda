{-# OPTIONS --safe --without-K #-}
module AoP.PermutedBrackets where

open import AoP.Prelude
open import AoP.Trees using (Tree)
open import AoP.BracketSpine using (leaves)
import AoP.BracketEnumeration as B
import AoP.Permutations as P
open import AoP.ListProduct using (collect; locate)
open import AoP.Naturality using (concat)
open import AoP.Horner using (map)
open import AoP.Subsequences using (_∈_)

-- Exercise 9.15. For associative, commutative operations we may
-- change the operand order as well as the parentheses. Repeated
-- operands still occupy separate leaves. Enumerate each permitted
-- order and then enumerate its full binary bracketings.
module Search {A : Set} where
  trees : List A → List (Tree A)
  trees xs = concat (map B.enumerate (P.perms xs))

  complete : ∀ {xs : List A} t → P.Perm xs (leaves t) → t ∈ trees xs
  complete t perm = collect B.enumerate (P.complete perm) (B.complete _ t refl)

  sound : ∀ xs {t} → t ∈ trees xs → P.Perm xs (leaves t)
  sound xs m with locate B.enumerate (P.perms xs) m
  ... | ys , p , q with B.sound ys q
  ...   | refl = P.sound xs p
