{-# OPTIONS --safe --without-K #-}
module AoP.QuarterUnique where

open import AoP.Prelude
open import AoP.QuarterCells using (even; Rounded)
open import AoP.QuarterDigits using (Cell; num; den)
open import AoP.QuarterRound using (round)
open import AoP.NatOrder using (_≤_; z≤; s≤; rid; chain; sum-mono)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- To justify reading the cell characterization in either direction,
-- show that the reference scanner must return any proposed cell which
-- contains the input. Half-open adjacent cells cannot share a point.
private
  mono : ∀ d {i j} → i ≤ j → even i d ≤ even j d
  mono d z≤ = z≤
  mono d (s≤ p) = sum-mono (rid d) (sum-mono (rid d) (mono d p))
  impossible : ∀ {n} {X : Set} → suc n ≤ n → X
  impossible {0} ()
  impossible {suc n} (s≤ p) = impossible p
  compare : ∀ i j → (i ≡ j) ⊎ ((suc i ≤ j) ⊎ (suc j ≤ i))
  compare 0 0 = inl refl
  compare 0 (suc j) = inr (inl (s≤ z≤))
  compare (suc i) 0 = inr (inr (s≤ z≤))
  compare (suc i) (suc j) with compare i j
  ... | inl eq = inl (cong suc eq)
  ... | inr (inl p) = inr (inl (s≤ p))
  ... | inr (inr p) = inr (inr (s≤ p))

unique : ∀ a d i j → Rounded a d i → Rounded a d j → i ≡ j
unique a d i j (li , ui) (lj , uj) with compare i j
... | inl eq = eq
... | inr (inl p) = impossible (chain ui (chain (mono d p) lj))
... | inr (inr p) = impossible (chain uj (chain (mono d p) li))

reads : ∀ ds k → Cell ds k → fst (round ds) ≡ k
reads ds k = unique (num ds) (den ds) _ k (snd (round ds))
