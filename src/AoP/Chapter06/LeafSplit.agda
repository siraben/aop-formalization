{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.LeafSplit where

open import AoP.Common.Prelude
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; rid; weaken)
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- Exercise 6.29. Store the keys at tips and allow an empty tree. A fork
-- now contributes no key of its own. Splitting [7] into [] and [7]
-- preserves the list and puts every left key below every right key, yet
-- the right recursive call receives [7] again. This is a failure of
-- the progress argument, even with an ordered input.
data LeafTree (A : Set) : Set where
  null : LeafTree A
  tip : A → LeafTree A
  fork : LeafTree A → LeafTree A → LeafTree A

flatten : ∀ {A} → LeafTree A → List A
flatten null = []
flatten (tip x) = x ∷ []
flatten (fork l r) = flatten l ++ flatten r

-- Arbitrarily many fork steps can represent the very same one key.
pad : ∀ {A} → Nat → A → LeafTree A
pad zero x = tip x
pad (suc n) x = fork null (pad n x)

unchanged : ∀ {A} n (x : A) → flatten (pad n x) ≡ x ∷ []
unchanged zero x = refl
unchanged (suc n) x = unchanged n x

len : ∀ {A : Set} → List A → Nat
len [] = 0
len (_ ∷ xs) = suc (len xs)

no-decrease : ∀ {A : Set} (x : A) → suc (len (x ∷ [])) ≤ len ([] ++ (x ∷ [])) → ⊥
no-decrease x (s≤ ())

-- A repair for contiguous splits: insist on two nonempty children.
-- Tip and null handle shorter inputs; every actual fork then decreases
-- both recursive lengths. Sorted merging needs its own correctness proof.
left-bound : ∀ {A : Set} (xs : List A) y ys → suc (len xs) ≤ len (xs ++ (y ∷ ys))
left-bound [] y ys = s≤ z≤
left-bound (_ ∷ xs) y ys = s≤ (left-bound xs y ys)

right-bound : ∀ {A : Set} (xs ys : List A) → len ys ≤ len (xs ++ ys)
right-bound [] ys = rid _
right-bound (_ ∷ xs) ys = weaken (right-bound xs ys)

progress : ∀ {A : Set} (x : A) xs y ys → let whole = (x ∷ xs) ++ (y ∷ ys) in
           (suc (len (x ∷ xs)) ≤ len whole) × (suc (len (y ∷ ys)) ≤ len whole)
progress x xs y ys = s≤ (left-bound xs y ys) , s≤ (right-bound xs (y ∷ ys))
