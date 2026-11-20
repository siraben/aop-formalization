{-# OPTIONS --safe --without-K #-}
module AoP.LayeredRowChoice where

open import AoP.Prelude
open import AoP.LayeredCostFold using (module Paths)
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.NatOrder using (_≤_; rid; chain; compare; sum-mono)
open import AoP.Polynomial using (inl; inr)
open import Agda.Builtin.Nat using (Nat)

-- §8.2: for a fixed new vertex, compare suffixes *after* charging
-- their incoming edge. Return the winning suffix and its certificate.
module Row {V : Set} (weight : V → V → Nat) (v : V) where
  open Paths weight
  score : Path → Nat
  score p = cost (via v p)
  record Best (xs : List Path) : Set where
    constructor winner
    field suffix : Path
          member : suffix ∈ xs
          lower : ∀ {p} → p ∈ xs → score suffix ≤ score p
  choose : ∀ p ps → Best (p ∷ ps)
  choose p [] = winner p here λ { here → rid _ ; (there ()) }
  choose p (q ∷ qs) with choose q qs
  ... | winner w at low with compare (score p) (score w)
  ... | inl le = winner p here λ { here → rid _ ; (there m) → chain le (low m) }
  ... | inr le = winner w (there at) λ { here → le ; (there m) → low m }

  -- One representative per old starting vertex suffices. The weight
  -- of the incoming edge is identical for a rival and its replacement.
  complete : ∀ {xs} (b : Best xs) (r : Path) → (Σ Path λ p → (p ∈ xs) × ((head p ≡ head r) × (cost p ≤ cost r))) → score (Best.suffix b) ≤ score r
  complete b r (p , at , same , le) = chain (Best.lower b at) extended
    where extended : score p ≤ score r
          extended rewrite same = sum-mono (rid _) le

module Trace where
  open import AoP.LayeredCostFold using (weight; root; w; e)
  open Row weight root
  result : Best.suffix (choose w (e ∷ [])) ≡ e
  result = refl
