{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.Selection where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; rid; chain; compare)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat)

-- §6.6 — Selection sorting. To emit the next output, choose a least
-- element and return the remaining input. It is not enough to prove a
-- lower bound: always emitting zero would pass that test. A removal
-- witness says *one occurrence* was actually taken, preserving the order
-- of the others. For [3,1,1] either occurrence of 1 is a valid minimum.
data Remove (m : Nat) : List Nat → List Nat → Set where
  head : ∀ {xs} → Remove m (m ∷ xs) xs
  past : ∀ {x xs ys} → Remove m xs ys → Remove m (x ∷ xs) (x ∷ ys)

data Lower (m : Nat) : List Nat → Set where
  empty : Lower m []
  below : ∀ {x xs} → m ≤ x → Lower m xs → Lower m (x ∷ xs)

weaken : ∀ {m n xs} → m ≤ n → Lower n xs → Lower m xs
weaken le empty = empty
weaken le (below p ps) = below (chain le p) (weaken le ps)

record Choice (xs : List Nat) : Set where
  constructor chose
  field
    minimum : Nat
    rest : List Nat
    removal : Remove minimum xs rest
    bound : Lower minimum xs

-- Compare the head with the least element of the nonempty tail. If the
-- head wins, leave the tail untouched; otherwise reuse the tail removal.
select : ∀ x xs → Choice (x ∷ xs)
select x [] = chose x [] head (below (rid x) empty)
select x (y ∷ ys) with select y ys
... | chose m zs rem b with compare x m
...   | inl le = chose x (y ∷ ys) head (below (rid x) (weaken le b))
...   | inr ge = chose m (x ∷ zs) (past rem) (below ge b)
