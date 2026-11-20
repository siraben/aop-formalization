{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.QuickWorstBound where

open import AoP.Common.Prelude
open import AoP.Chapter06.Quicksort
open import AoP.Chapter06.QuickSplitWork using (pass; pass-size; work)
open import AoP.Chapter06.SelectionSort using (length)
open import AoP.Chapter06.SelectionTotalCost using (tri)
open import AoP.Common.NatOrder using (_≤_; rid; chain; sum-mono; weaken)
open import Agda.Builtin.Nat using (Nat; suc; _+_)

private
  move : ∀ a b → a + suc b ≡ suc (a + b)
  move 0 b = refl
  move (suc a) b = cong suc (move a b)
  assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)
  assoc 0 b c = refl
  assoc (suc a) b c = cong suc (assoc a b c)
  room : ∀ a b → a ≤ a + b
  room 0 b = AoP.Common.NatOrder.z≤
  room (suc a) b = AoP.Common.NatOrder.s≤ (room a b)
  combine : ∀ a b → tri a + tri b ≤ tri (a + b)
  combine 0 b = rid _
  combine (suc a) b rewrite assoc a (tri a) (tri b) = sum-mono (room a b) (combine a b)

-- Each comparison places one occurrence in exactly one child. Thus
-- their lengths sum to the pass cost, even when equal keys are split.
partition-size : ∀ {p xs l r} (s : Split p xs l r) → length l + length r ≡ pass s
partition-size (pivot _) = refl
partition-size (left _ s) = cong suc (partition-size s)
partition-size (right {l = l} {r = r} _ s) = move (length l) (length r) ∙ cong suc (partition-size s)

bound : ∀ {xs} (t : Tree xs) → work t ≤ tri (length xs)
bound null = rid 0
bound (fork {l = l} {r = r} p s lt rt) with sum-mono (rid (pass s)) (chain (sum-mono (bound lt) (bound rt)) (combine (length l) (length r)))
... | le rewrite partition-size s = cast (cong tri (pass-size s)) le
  where cast : ∀ {a b c : Nat} → b ≡ c → a ≤ b → a ≤ c
        cast refl q = q
