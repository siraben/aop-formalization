{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.SelectionUnique where

open import AoP.Common.Prelude
open import AoP.Chapter06.Selection
open import AoP.Chapter06.SelectionSort using (length; loop; shorter; remaining)
open import AoP.Chapter06.SelectionEquation using (sort)
open import AoP.Common.NatOrder using (_≤_; s≤; rid)
open import Agda.Builtin.Nat using (Nat; suc)

-- §6.6. The selected occurrence is removed before the next call, so
-- each defining equation is forced by equations at shorter lists.
module Law (f : List Nat → List Nat) (base : f [] ≡ [])
  (step : ∀ x xs → let c = select x xs in f (x ∷ xs) ≡ Choice.minimum c ∷ f (Choice.rest c)) where
  bounded : ∀ n xs (p : length xs ≤ n) → f xs ≡ fst (loop n xs p)
  bounded n [] p = base
  bounded (suc n) (x ∷ xs) (s≤ p) with select x xs | step x xs
  ... | chose k rs rem lb | unfold = begin
    f (x ∷ xs) ≡⟨ unfold ⟩
    k ∷ f rs ≡⟨ cong (k ∷_) (bounded n rs (remaining (shorter rem) p)) ⟩
    k ∷ fst (loop n rs (remaining (shorter rem) p)) ∎

  unique : ∀ xs → f xs ≡ sort xs
  unique xs = bounded (length xs) xs (rid _)
