{-# OPTIONS --safe --without-K #-}
module AoP.SorterAgreement where

open import AoP.Prelude
open import AoP.SortedBagUnique using (dec; unique)
open import AoP.BagCountPermutation using (module Law)
open import AoP.Selection using (Remove; head; past)
open import AoP.SelectionSort using (Result; Perm; finish; emit; selection-sort)
open import AoP.Permutations using (Insert; front; later)
open import AoP.QuickOrdered using (certified)
open import AoP.Quicksort using (quicksort)
open import AoP.InsertionSort using (sort)
open import Agda.Builtin.Nat using (Nat)
open Law dec
private
  ins : ∀ {x : Nat} {xs ys} → Remove x ys xs → Insert x xs ys
  ins head = front
  ins (past r) = later (ins r)
  counts : ∀ {xs ys} → Perm xs ys → Same xs ys
  counts finish a = refl
  counts (emit {m} r p) a = increment (ins r) a ∙ cong (bump a m) (counts p a)
  sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  sym refl = refl

agree : ∀ xs (s t : Result xs) → fst s ≡ fst t
agree xs (ys , p , sy) (zs , q , sz) = unique ys zs sy sz (λ a → sym (counts p a) ∙ counts q a)

quick-selection : ∀ xs → quicksort xs ≡ fst (selection-sort xs)
quick-selection xs = agree xs (certified xs) (selection-sort xs)
quick-insertion : ∀ xs → quicksort xs ≡ fst (sort xs)
quick-insertion xs = agree xs (certified xs) (sort xs)
