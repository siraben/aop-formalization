{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.TeXGridMinimum where

open import AoP.Common.Prelude
open import AoP.Chapter10.OpenUpperDigit using (Upper)
open import AoP.Chapter10.StrictUpperQuotient using (choose; strict)
open import AoP.Chapter10.TeXIntervalGrowth using (scale; at-five)
open import AoP.Chapter10.TeXFirstGrid using (Answer; scan)
open import Agda.Builtin.Nat using (Nat; suc)

-- Compute the first occupied decimal grid directly from its integer
-- endpoints. The upper numerator stays positive under multiplication
-- by ten, so strict division applies at every width.
module Positive (lower : Nat) where
  L = λ k → scale k lower
  H = λ k → scale k (2 + lower)
    where open import Agda.Builtin.Nat using (_+_)
  upper-pred : ∀ k → Σ Nat (λ m → suc m ≡ H k)
  upper-pred 0 = suc lower , refl
  upper-pred (suc k) with upper-pred k
  ... | m , eq = (9 + m * 10) , cong (_* 10) eq
    where open import Agda.Builtin.Nat using (_+_; _*_)
  prefix : Nat → Nat
  prefix k = choose 131071 (fst (upper-pred k))
  cell : ∀ k → Upper 131072 (H k) (prefix k)
  cell k = change (snd (upper-pred k)) (strict 131071 (fst (upper-pred k)))
    where change : ∀ {x y} → x ≡ y → Upper 131072 x (prefix k) → Upper 131072 y (prefix k)
          change refl u = u
  optimum : Answer 131072 L H
  optimum = scan 5 131072 L H prefix cell (at-five lower (prefix 5) (cell 5))
