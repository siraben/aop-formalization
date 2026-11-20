{-# OPTIONS --safe --without-K #-}
module AoP.VanHeadOrder where

open import AoP.Prelude
open import Agda.Builtin.Nat using (Nat; suc)
open import AoP.NatOrder using (_≤_; s≤)
open import AoP.ConversionCost using (len)
open import AoP.Paragraph using (Nonempty; _∷⁺_; module Layout)

-- Exercise 7.53, nonempty partitions. When comparing two updates,
-- opening a block always puts the singleton [a] at the head. It is
-- also a prefix of every first block produced by extending with a.
module Law (A : Set) where
  open Layout (λ (_ : A) → 0) 0 using (Para; new; glue)
  data Prefix : List A → List A → Set where
    empty : ∀ {xs} → Prefix [] xs
    keep : ∀ a {xs ys} → Prefix xs ys → Prefix (a ∷ xs) (a ∷ ys)
  first-block : Para → List A
  first-block ((a ∷⁺ xs) ∷⁺ _) = a ∷ xs
  H : Para → Para → Set
  H p q = Prefix (first-block p) (first-block q)

  new-new : ∀ a p q → H (new a p) (new a q)
  new-new a p q = keep a empty
  new-old : ∀ a p q → H (new a p) (glue a q)
  new-old a p ((x ∷⁺ xs) ∷⁺ ys) = keep a empty

  -- (7.20): starting with strictly fewer blocks leaves room to open
  -- one new block and still use at most as many as the extended plan.
  count : Para → Nat
  count (_ ∷⁺ bs) = suc (len bs)
  new-count : ∀ a p q → suc (count p) ≤ count q → count (new a p) ≤ count (glue a q)
  new-count a (l ∷⁺ ls) ((x ∷⁺ xs) ∷⁺ ys) le = le
