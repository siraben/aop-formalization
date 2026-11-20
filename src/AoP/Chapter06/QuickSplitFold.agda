{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.QuickSplitFold where

open import AoP.Common.Prelude
open import AoP.Chapter06.Quicksort using (split)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Common.NatOrder using (compare)
open import Agda.Builtin.Nat using (Nat)

-- §6.6. Project the executable splitter's trace away. What remains is
-- a nonempty-list fold: a singleton supplies the pivot and each prepend
-- updates just one partition. No empty-input pivot is needed.
fold⁺ : ∀ {A B : Set} → (A → B) → (A → B → B) → A → List A → B
fold⁺ base step x [] = base x
fold⁺ base step x (y ∷ ys) = step x (fold⁺ base step y ys)
Parts = Nat × (List Nat × List Nat)
base : Nat → Parts
base p = p , [] , []
step : Nat → Parts → Parts
step x (p , l , r) with compare x p
... | inl _ = p , x ∷ l , r
... | inr _ = p , l , x ∷ r

project : Nat → List Nat → Parts
project x xs with split x xs
... | p , l , r , _ = p , l , r

prepend : ∀ x y ys → project x (y ∷ ys) ≡ step x (project y ys)
prepend x y ys with split y ys
... | p , l , r , s with compare x p
...   | inl _ = refl
...   | inr _ = refl
fusion : ∀ x xs → project x xs ≡ fold⁺ base step x xs
fusion x [] = refl
fusion x (y ∷ ys) = begin
  project x (y ∷ ys) ≡⟨ prepend x y ys ⟩
  step x (project y ys) ≡⟨ cong (step x) (fusion y ys) ⟩
  fold⁺ base step x (y ∷ ys) ∎
