{-# OPTIONS --safe --without-K #-}
module AoP.ListMemberPath where

open import AoP.Prelude
open import AoP.Relations
open import AoP.TreeMemberPath using (Path; stop; via)
open import AoP.Subsequences using (_∈_; here; there)

-- Exercise 6.17, the intermediate equation inlist = head ∘ tail*.
-- A successful search drops one cell per `there`, then reads the head.
-- A path reaching the empty suffix cannot supply the required head.
data Tail {A : Set} : List A ← List A where
  drop : ∀ {x xs} → Tail xs (x ∷ xs)

data Head {A : Set} : A ← List A where
  read : ∀ {x xs} → Head x (x ∷ xs)

find : ∀ {A} → _∈_ {A} ⊆ Head ∘ Path Tail
find here = _ , read , stop
find (there p) with find p
... | suffix , h , path = suffix , h , via drop path

follow : ∀ {A} {xs ys : List A} {x} → Path Tail ys xs → Head x ys → x ∈ xs
follow stop read = here
follow (via drop path) h = there (follow path h)

sound : ∀ {A} → Head ∘ Path Tail ⊆ _∈_ {A}
sound (_ , h , path) = follow path h
