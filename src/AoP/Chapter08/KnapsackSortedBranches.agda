{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.KnapsackSortedBranches where

open import AoP.Common.Prelude
open import AoP.Chapter08.KnapsackFrontier using (Summary; value; weight; _⊞_)
open import AoP.Chapter06.OrderedMeet using (module Order)
open import AoP.Chapter08.SortedImage using (module Law)
open import AoP.Chapter08.SortedFilter using (module Restrict)
open import AoP.Chapter08.SortedSubset using (module Sort)
open import AoP.Chapter07.FilterGreedy using () renaming (module Law to Filter)
open import AoP.Chapter03.Horner using (map)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; sum-mono; rid)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat; suc)

-- §8.4. Sorting once per branch would be redundant: adding a common
-- value preserves the descending comparisons, then filtering for
-- capacity only removes entries. The skip branch is unchanged.
Desc : Summary → Summary → Set
Desc p q = value q ≤ value p
fits? : ∀ w cap → (w ≤ cap) ⊎ (w ≤ cap → ⊥)
fits? 0 cap = inl z≤
fits? (suc w) 0 = inr λ ()
fits? (suc w) (suc cap) with fits? w cap
... | inl p = inl (s≤ p)
... | inr no = inr λ { (s≤ p) → no p }
module Branch (cap : Nat) (i : Summary) where
  Fits : Summary → Set
  Fits p = weight p ≤ cap
  test = λ p → fits? (weight p) cap
  open Filter Fits test using (filter)
  open Law (i ⊞_) Desc using (pull; ordered)
  take : List Summary → List Summary
  take xs = filter (map (i ⊞_) xs)
  private
    lift : ∀ {xs} → Order.Ordered Desc xs → Order.Ordered pull xs
    lift Order.nil = Order.nil
    lift (Order.cons lower rest) = Order.cons (λ m → sum-mono (rid (value i)) (lower m)) (lift rest)
  take-order : ∀ {xs} → Order.Ordered Desc xs → Order.Ordered Desc (take xs)
  take-order {xs} ord = Sort.ordered-sub Desc (Restrict.sub Desc Fits test _) (ordered (lift ord))

-- From alternatives worth 5, 4 and 0, extending by (2,3) produces
-- values 8,7,3. At capacity 3 only the last two survive, still sorted.
worked : Branch.take 3 (2 , 3) ((3 , 5) ∷ (1 , 4) ∷ (0 , 0) ∷ []) ≡ (3 , 7) ∷ (2 , 3) ∷ []
worked = refl
