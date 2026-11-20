{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.MinimalInclusion where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter07.MinimalComparison using (Test; Point; low; mid; high; Order; same; strict)
open import AoP.Chapter08.Thinning using (Min)

-- Exercise 7.21. Under equality every point is minimal. Add the
-- strict comparison low ≤ high: high acquires a predecessor that
-- it does not precede, so it loses minimality on the same input set.
Equal : Point ← Point
Equal = _≡_

included : Equal ⊆ Order
included refl = same

full : Point → Set
full _ = ⊤

before : Min (Test Equal) high full
before = tt , λ { _ _ refl → refl }

after : Min (Test Order) high full → ⊥
after (_ , lower) with lower low tt strict
... | ()

not-monotone : (∀ a X → Min (Test Equal) a X → Min (Test Order) a X) → ⊥
not-monotone sub = after (sub high full before)
