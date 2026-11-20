{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.BlockHeadCover where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter08.Thinning using (Thin; thin)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Chapter08.LeftMinimumCount using (module Law)
open import AoP.Chapter08.LeftMinimumFusion using (module Fuse)

-- Exercise 8.15. The heads of *any* admissible partition form a
-- thinning. In the extend case the skipped item is represented by
-- the current head, which remains present until the block closes.
module Proof {A : Set} (Q : A → A → Set) (rr : ∀ a → Q a a)
             (tr : ∀ {a b c} → Q a b → Q b c → Q a c)
             (test : ∀ a b → Q a b ⊎ (Q a b → ⊥)) where
  open Law Q rr tr test
  open Fuse Q rr tr test
  first : ∀ {h xs n} (p : Cuts h xs n) → h ∈ heads p
  first done = here
  first (extend hx p) = first p
  first (split p) = here

  members : ∀ {h xs n a} (p : Cuts h xs n) → a ∈ heads p → a ∈ (h ∷ xs)
  members done m = m
  members (split p) here = here
  members (split p) (there m) = there (members p m)
  members (extend hx p) m with members p m
  ... | here = here
  ... | there rest = there (there rest)

  cover : ∀ {h xs n} (p : Cuts h xs n) b → b ∈ (h ∷ xs) → Σ A λ a → (a ∈ heads p) × Q a b
  cover {h} p .h here = h , first p , rr h
  cover done b (there ())
  cover (extend hx p) b (there here) = _ , first p , hx
  cover (extend hx p) b (there (there m)) = cover p b (there m)
  cover (split p) b (there m) with cover p b m
  ... | a , kept , edge = a , there kept , edge

  correct : ∀ h xs → Thin Q (_∈ run h xs) (_∈ (h ∷ xs))
  correct h xs with run h xs | fusion h xs
  ... | ._ | refl = thin (members p) (cover p)
    where p = snd (greedy h xs)
