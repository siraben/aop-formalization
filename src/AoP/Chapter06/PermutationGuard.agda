{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.PermutationGuard where

open import AoP.Common.Prelude
open import AoP.Chapter05.Permutations using (Insert; front; later; Perm; empty; insert)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Chapter04.Relations using (_←_; _∘_; _⊆_)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)

-- Exercise 6.22. Distinguish the newly inserted occurrence from all
-- older ones. This works even when their values are equal.
module Guard {A : Set} where
  locate : ∀ {a b : A} {xs ys} → Insert a xs ys → b ∈ ys → (b ≡ a) ⊎ (b ∈ xs)
  locate front here = inl refl
  locate front (there m) = inr m
  locate (later i) here = inr here
  locate (later i) (there m) with locate i m
  ... | inl eq = inl eq
  ... | inr old = inr (there old)

  keep : ∀ {a b : A} {xs ys} → Insert a xs ys → b ∈ xs → b ∈ ys
  keep front m = there m
  keep (later i) here = here
  keep (later i) (there m) = there (keep i m)

  new : ∀ {a : A} {xs ys} → Insert a xs ys → a ∈ ys
  new front = here
  new (later i) = there (new i)

  forward : ∀ {b : A} {xs ys} → Perm xs ys → b ∈ xs → b ∈ ys
  forward (insert p i) here = new i
  forward (insert p i) (there m) = keep i (forward p m)

  backward : ∀ {b : A} {xs ys} → Perm xs ys → b ∈ ys → b ∈ xs
  backward (insert p i) m with locate i m
  ... | inl refl = here
  ... | inr old = there (backward p old)

  identity : ∀ (xs : List A) → Perm xs xs
  identity [] = empty
  identity (_ ∷ xs) = insert (identity xs) front

  perm : List A ← List A
  perm ys xs = Perm xs ys

  member-law : _∈_ ∘ perm ⊆ _∈_
  member-law (_ , m , p) = backward p m

  member-intro : _∈_ ⊆ _∈_ ∘ perm
  member-intro m = _ , m , identity _

  -- ok tests that the candidate bounds every member of its remainder.
  -- Lifting permutation to pairs leaves the candidate fixed.
  module Minimum (R : A ← A) where
    Pair = A × List A
    ok : Pair ← Pair
    ok y x = (y ≡ x) × (∀ {a} → a ∈ snd x → R (fst x) a)
    lift : Pair ← Pair
    lift (b , ys) (a , xs) = (b ≡ a) × Perm xs ys

    open import AoP.Chapter04.Relations using (_／_; _˘; _⊓_)
    open import AoP.Chapter04.Shunting using (Id; graph)

    -- Division says that R relates the candidate to every member of
    -- the list. Feed the two projections through this relation, then
    -- intersect with identity to retain precisely the passing pairs.
    test : Pair ← Pair
    test = Id ⊓ (graph fst ˘ ∘ ((R ／ (_∈_ ˘)) ∘ graph snd))

    express : ok ⊆ test
    express (refl , bound) = refl , _ , refl , _ , bound , refl

    interpret : test ⊆ ok
    interpret (refl , _ , refl , _ , bound , refl) = refl , bound

    commute : lift ∘ ok ⊆ ok ∘ lift
    commute (_ , (eq , p) , refl , bound) = _ , (refl , (λ m → subst _ (sym eq) (bound (backward p m)))) , eq , p
      where
      sym : ∀ {a b : A} → a ≡ b → b ≡ a
      sym refl = refl
      subst : ∀ {a b : A} (P : A → Set) → a ≡ b → P a → P b
      subst P refl v = v

    reverse : ok ∘ lift ⊆ lift ∘ ok
    reverse (_ , (refl , bound) , refl , p) = _ , (refl , p) , refl , λ m → bound (forward p m)
