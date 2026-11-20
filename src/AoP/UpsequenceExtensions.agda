{-# OPTIONS --safe --without-K #-}
module AoP.UpsequenceExtensions where

open import AoP.Prelude
open import AoP.UpsequenceFrontier using (extensions)
open import AoP.UpsequenceDominance using (module Law)
open import AoP.ParagraphMinimum using (le?)
open import AoP.Polynomial using (inl; inr)
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.NatOrder using (_≤_)
open import Agda.Builtin.Nat using (Nat)
open Law _≤_

-- The take branch enumerates exactly those old candidates whose head
-- accepts the new element. Recover the old candidate from any result.
intro : ∀ a ys {xs} → xs ∈ ys → Accept a xs → (a ∷ xs) ∈ extensions a ys
intro a ([] ∷ ys) here ok = here
intro a ([] ∷ ys) (there m) ok = there (intro a ys m ok)
intro a ((b ∷ bs) ∷ ys) m ok with le? a b | m
... | inl p | here = here
... | inr no | here with no ok
...   | ()
intro a ((b ∷ bs) ∷ ys) m ok | inl p | there n = there (intro a ys n ok)
intro a ((b ∷ bs) ∷ ys) m ok | inr no | there n = intro a ys n ok

From : Nat → List (List Nat) → List Nat → Set
From a ys zs = Σ (List Nat) λ xs → (xs ∈ ys) × Accept a xs × (zs ≡ a ∷ xs)

lift : ∀ a y ys zs → From a ys zs → From a (y ∷ ys) zs
lift a y ys zs (x , m , ok , eq) = x , there m , ok , eq

elim : ∀ a ys {zs} → zs ∈ extensions a ys → From a ys zs
elim a ([] ∷ ys) here = [] , here , tt , refl
elim a ([] ∷ ys) (there m) = lift a [] ys _ (elim a ys m)
elim a ((b ∷ bs) ∷ ys) m with le? a b
... | inr no = lift a (b ∷ bs) ys _ (elim a ys m)
... | inl ok with m
...   | here = (b ∷ bs) , here , ok , refl
...   | there n = lift a (b ∷ bs) ys _ (elim a ys n)
