{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.QuarterRound where

open import AoP.Common.Prelude
open import AoP.Chapter03.QuarterCells using (even; Rounded)
open import AoP.Chapter03.QuarterDigits using (num; den; Cell)
open import AoP.Chapter03.TeXFraction using (Digit)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; rid; chain; weaken)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

private
  cut : ∀ x y → (x ≤ y) ⊎ (suc y ≤ x)
  cut 0 y = inl z≤
  cut (suc x) 0 = inr (s≤ z≤)
  cut (suc x) (suc y) with cut x y
  ... | inl p = inl (s≤ p)
  ... | inr p = inr (s≤ p)
  pad : ∀ n x → x ≤ n + x
  pad 0 x = rid x
  pad (suc n) x = weaken (pad n x)
  grows : ∀ k d → 1 ≤ d → suc (even k d) ≤ even (suc k) d
  grows k (suc n) p = s≤ (chain (pad (suc n) (even k (suc n))) (pad n _))
  positive : ∀ ds → 1 ≤ den ds
  positive [] = rid 1
  positive (h ∷ ds) = chain (positive ds) (room (den ds) (9 * den ds))
    where room : ∀ n x → n ≤ n + x
          room 0 x = z≤
          room (suc n) x = s≤ (room n x)

-- Reference integer division by a positive 2d. Advancing the scaled
-- numerator by one either stays in the same cell or crosses precisely
-- its right endpoint. This simple scanner makes no efficiency claim.
scan : ∀ d → 1 ≤ d → ∀ n → Σ Nat λ k → (even k d ≤ n) × (suc n ≤ even (suc k) d)
scan d pos 0 = 0 , z≤ , grows 0 d pos
scan d pos (suc n) with scan d pos n
... | k , lo , hi with cut (even (suc k) d) (suc n)
...   | inl crossed = suc k , crossed , chain (s≤ hi) (grows (suc k) d pos)
...   | inr inside = k , weaken lo , inside

round : ∀ ds → Σ Nat (Cell ds)
round ds = scan (den ds) (positive ds) (den ds + 8 * num ds)
