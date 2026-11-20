{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.PermutedBrackets where

open import AoP.Common.Prelude
open import AoP.Chapter01.Trees using (Tree)
open import AoP.Chapter09.BracketSpine using (leaves)
import AoP.Chapter09.BracketEnumeration as B
import AoP.Chapter05.Permutations as P
open import AoP.Appendix.ListProduct using (collect; locate)
open import AoP.Chapter01.Naturality using (concat)
open import AoP.Chapter03.Horner using (map)
open import AoP.Chapter05.Subsequences using (_∈_)

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
