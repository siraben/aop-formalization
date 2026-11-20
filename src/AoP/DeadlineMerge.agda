{-# OPTIONS --safe --without-K #-}
module AoP.DeadlineMerge where

open import AoP.Prelude
open import AoP.Tardiness using (Job)
open import AoP.NatOrder using (_≤_; compare; s≤; z≤)
open import AoP.ConversionCost using (len)
open import AoP.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat; suc)
open Job

-- Merge two due-date-ordered runs. Each comparison emits one job;
-- once either run is empty, append the remainder without comparisons.
data Trace : List Job → List Job → List Job → Set where
  left-empty : ∀ ys → Trace [] ys ys
  right-empty : ∀ xs → Trace xs [] xs
  left : ∀ {x xs y ys zs} → due x ≤ due y → Trace xs (y ∷ ys) zs → Trace (x ∷ xs) (y ∷ ys) (x ∷ zs)
  right : ∀ {x xs y ys zs} → due y ≤ due x → Trace (x ∷ xs) ys zs → Trace (x ∷ xs) (y ∷ ys) (y ∷ zs)

merge : ∀ xs ys → Σ _ (Trace xs ys)
merge [] ys = ys , left-empty ys
merge (x ∷ xs) = walk
  where walk : ∀ ys → Σ _ (Trace (x ∷ xs) ys)
        walk [] = _ , right-empty _
        walk (y ∷ ys) with compare (due x) (due y)
        ... | inl p with merge xs (y ∷ ys)
        ...   | zs , tr = x ∷ zs , left p tr
        walk (y ∷ ys) | inr p with walk ys
        ...   | zs , tr = y ∷ zs , right p tr

tests : ∀ {xs ys zs} → Trace xs ys zs → Nat
tests (left-empty _) = 0
tests (right-empty _) = 0
tests (left _ m) = suc (tests m)
tests (right _ m) = suc (tests m)
linear : ∀ {xs ys zs} (m : Trace xs ys zs) → tests m ≤ len zs
linear (left-empty _) = z≤
linear (right-empty _) = z≤
linear (left _ m) = s≤ (linear m)
linear (right _ m) = s≤ (linear m)
