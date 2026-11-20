{-# OPTIONS --safe --without-K #-}
module AoP.StrictUpperQuotient where

open import AoP.Prelude
open import AoP.DigitInterval using (Cell)
open import AoP.OpenUpperDigit using (Upper; correct; only)
open import AoP.DivisionThreshold using (sound; complete)
open import AoP.NatOrder using (_≤_; z≤; s≤; rid)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat; suc; div-helper; _*_)

-- Exercise 10.14. For positive numerator N = m+1 and width w = k+1,
-- run the primitive on m. Its two threshold implications supply both
-- inequalities of the open-upper cell, even when N is divisible by w.
choose : Nat → Nat → Nat
choose k m = div-helper 0 k m k
private
  impossible : ∀ t → suc t ≤ t → ⊥
  impossible 0 ()
  impossible (suc t) (s≤ p) = impossible t p
  flip : ∀ a b → (a ≤ b → ⊥) → suc b ≤ a
  flip 0 b no with no z≤
  ... | ()
  flip (suc a) 0 no = s≤ z≤
  flip (suc a) (suc b) no = s≤ (flip a b (λ p → no (s≤ p)))

cell : ∀ k m → Cell (suc k) m (choose k m)
cell k m = lower (choose k m) (rid _) , flip (suc d * suc k) m (λ p → impossible d (complete k m k (suc d) p))
  where d = choose k m
        lower : ∀ t → t ≤ d → t * suc k ≤ m
        lower 0 _ = z≤
        lower (suc t) p = sound k m k (suc t) p

strict : ∀ k m → Upper (suc k) (suc m) (choose k m)
strict k m = correct (suc k) m (choose k m) (cell k m)
unique-choice : ∀ k m d → Upper (suc k) (suc m) d → choose k m ≡ d
unique-choice k m d p = only (suc k) m (choose k m) d (strict k m) p

-- Upper endpoint 5 exactly: division of 10q would return 5, while
-- division of its predecessor returns 4 as required by strictness.
endpoint : choose 131071 655359 ≡ 4
endpoint = refl
