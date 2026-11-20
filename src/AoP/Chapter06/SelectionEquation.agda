{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.SelectionEquation where

open import AoP.Common.Prelude
open import AoP.Chapter06.Selection
open import AoP.Chapter06.SelectionSort using (length; loop; shorter; remaining; selection-sort)
open import AoP.Common.NatOrder using (_≤_; s≤; rid)
open import Agda.Builtin.Nat using (Nat; suc)

-- §6.6. Fuel bounds justify recursion but do not choose the answer.
-- Every sufficiently large budget implements the same selection step.
independent : ∀ n m xs (p : length xs ≤ n) (q : length xs ≤ m) → fst (loop n xs p) ≡ fst (loop m xs q)
independent n m [] p q = refl
independent (suc n) (suc m) (x ∷ xs) (s≤ p) (s≤ q) with select x xs
... | chose k rs rem lb = cong (k ∷_) (independent n m rs (remaining (shorter rem) p) (remaining (shorter rem) q))

sort : List Nat → List Nat
sort xs = fst (selection-sort xs)
step : ∀ x xs → let c = select x xs in sort (x ∷ xs) ≡ Choice.minimum c ∷ sort (Choice.rest c)
step x xs with select x xs
... | chose k rs rem lb = cong (k ∷_) (independent (length xs) (length rs) rs (remaining (shorter rem) (rid _)) (rid _))
