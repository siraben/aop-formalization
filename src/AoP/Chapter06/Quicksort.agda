{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.Quicksort where

open import AoP.Common.Prelude
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; rid; weaken; chain; compare)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter06.SelectionSort using (length)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- §6.6. Sort by unfolding a list into a pivot tree, then reading its
-- labels in order. The split is a right fold on a nonempty list: the
-- last element supplies the pivot and each earlier item goes to one
-- side. The trace records each input occurrence, including equal keys.
data Split : Nat → List Nat → List Nat → List Nat → Set where
  pivot : ∀ p → Split p (p ∷ []) [] []
  left : ∀ {x p xs l r} → x ≤ p → Split p xs l r → Split p (x ∷ xs) (x ∷ l) r
  right : ∀ {x p xs l r} → p ≤ x → Split p xs l r → Split p (x ∷ xs) l (x ∷ r)

split : ∀ x xs → Σ Nat λ p → Σ _ λ l → Σ _ λ r → Split p (x ∷ xs) l r
split x [] = x , [] , [] , pivot x
split x (y ∷ ys) with split y ys
... | p , l , r , trace with compare x p
...   | inl le = p , x ∷ l , r , left le trace
...   | inr ge = p , l , x ∷ r , right ge trace

smaller : ∀ {p xs l r} → Split p xs l r →
          (suc (length l) ≤ length xs) × (suc (length r) ≤ length xs)
smaller (pivot _) = rid 1 , rid 1
smaller (left _ s) = s≤ (fst (smaller s)) , weaken (snd (smaller s))
smaller (right _ s) = weaken (fst (smaller s)) , s≤ (snd (smaller s))

-- The index and split witnesses retain the relation between the original
-- list and the intermediate tree without comparing sorted outputs.
data Tree : List Nat → Set where
  null : Tree []
  fork : ∀ {xs l r} p → Split p xs l r → Tree l → Tree r → Tree xs

unfold : ∀ n xs → length xs ≤ n → Tree xs
unfold n [] bound = null
unfold (suc n) (x ∷ xs) (s≤ bound) with split x xs
... | p , l , r , s with smaller s
...   | s≤ lb , s≤ rb = fork p s (unfold n l (chain lb bound)) (unfold n r (chain rb bound))

flatten : ∀ {xs} → Tree xs → List Nat
flatten null = []
flatten (fork p _ l r) = flatten l ++ (p ∷ flatten r)

quicksort : List Nat → List Nat
quicksort xs = flatten (unfold (length xs) xs (rid _))

-- The root pivot is 2, with [1,2] on its left and [3] on its right.
duplicates : quicksort (3 ∷ 1 ∷ 2 ∷ 2 ∷ []) ≡ 1 ∷ 2 ∷ 2 ∷ 3 ∷ []
duplicates = refl
