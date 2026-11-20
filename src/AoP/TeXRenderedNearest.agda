{-# OPTIONS --safe --without-K #-}
module AoP.TeXRenderedNearest where

open import AoP.Prelude
open import AoP.TeXRenderWidth using (render)
open import AoP.TeXNearestFeasible using (module Select)
open import AoP.TeXNearestNeighbours using (err)
open import AoP.TeXDistanceScale using (power)
open import AoP.TeXClosestShortest using (numerator)
open import AoP.TeXExternal using (length)
open import AoP.TeXFraction using (Digit)
open import AoP.NatOrder using (_≤_; s≤; z≤; rid)
open import Agda.Builtin.Nat using (Nat; suc; _*_)

-- Package the constrained minimizer as actual fixed-width digits. Use
-- the predecessor of 10^k as cap, so rendering cannot overflow.
module At (k L h target : Nat) where
  pred : Nat → Nat
  pred 0 = 0
  pred (suc n) = n
  pos : ∀ n → 1 ≤ power n
  pos 0 = s≤ z≤
  pos (suc n) = first (power n) (pos n)
    where first : ∀ v → 1 ≤ v → 1 ≤ 10 * v
          first (suc v) _ = s≤ z≤
  fit : ∀ n i → 1 ≤ n → i ≤ pred n → suc i ≤ n
  fit (suc n) i _ p = s≤ p
  module S = Select 131071 65535 L h (pred (power k)) target
  open S using (module R; cost)
  record Result : Set where
    constructor result
    field ds : List Digit
          at-width : length ds ≡ k
          admissible : R.Exactly (numerator ds)
          minimum : ∀ j → R.Exactly j → cost (numerator ds) ≤ cost j
  solve : ∀ base → R.Exactly base → Result
  solve base ok = emit (S.solve base ok)
    where
    emit : Σ Nat (λ i → R.Exactly i × (∀ j → R.Exactly j → cost i ≤ cost j)) → Result
    emit (i , (valid , best)) = finish (render k i (fit (power k) i (pos k) (snd valid)))
      where finish : Σ (List Digit) (λ ds → (length ds ≡ k) × (numerator ds ≡ i)) → Result
            finish (ds , (w , eq)) = result ds w (sub R.Exactly eq valid) (λ j yes → sub (λ a → cost a ≤ cost j) eq (best j yes))
              where sub : (P : Nat → Set) → ∀ {a b} → a ≡ b → P b → P a
                    sub P refl p = p
