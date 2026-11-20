{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.SelectionSort where

open import AoP.Chapter06.Selection
open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; s≤; rid)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- §6.6. After each minimum selection the remaining list is smaller, but
-- it need not be the original tail. Use length to justify termination.
-- Perm records one removal per output slot, hence preserves duplicates.
data Perm : List Nat → List Nat → Set where
  finish : Perm [] []
  emit : ∀ {m xs rest ys} → Remove m xs rest → Perm rest ys → Perm xs (m ∷ ys)

data Sorted : List Nat → Set where
  nil : Sorted []
  cons : ∀ {m ys} → Lower m ys → Sorted ys → Sorted (m ∷ ys)

remove-bound : ∀ {k m xs rs} → Remove m xs rs → Lower k xs → (k ≤ m) × Lower k rs
remove-bound head (below km b) = km , b
remove-bound (past r) (below kx b) with remove-bound r b
... | km , rest = km , below kx rest

perm-bound : ∀ {k xs ys} → Perm xs ys → Lower k xs → Lower k ys
perm-bound finish empty = empty
perm-bound (emit r p) b with remove-bound r b
... | km , rest = below km (perm-bound p rest)

length : List Nat → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

shorter : ∀ {m xs rs} → Remove m xs rs → length xs ≡ suc (length rs)
shorter head = refl
shorter (past r) = cong suc (shorter r)

remaining : ∀ {a b n} → suc a ≡ suc b → a ≤ n → b ≤ n
remaining refl p = p

Result : List Nat → Set
Result xs = Σ (List Nat) λ ys → Perm xs ys × Sorted ys

loop : ∀ n xs → length xs ≤ n → Result xs
loop n [] b = [] , finish , nil
loop (suc n) (x ∷ xs) (s≤ budget) with select x xs
... | chose m rs r lb with loop n rs (remaining (shorter r) budget)
...   | ys , p , sorted = (m ∷ ys) , emit r p , cons (perm-bound p (snd (remove-bound r lb))) sorted

selection-sort : ∀ xs → Result xs
selection-sort xs = loop (length xs) xs (rid _)
