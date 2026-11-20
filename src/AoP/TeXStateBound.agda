{-# OPTIONS --safe --without-K #-}
module AoP.TeXStateBound where

open import AoP.Prelude
open import AoP.NatOrder using (_≤_; z≤; s≤; rid; chain; sum-mono)
open import AoP.TeXFraction using (Digit; cshift)
open import AoP.DivisionThreshold using (sound)
open import AoP.Complement using (⊥)
open import AoP.Folds using (⦅_∣_⦆)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)

-- The executable suffix accumulator fits in seventeen bits. Even the
-- largest digit, 9, leaves the shifted numerator below 10 * 131072.
private
  mul : ∀ n {x y} → x ≤ y → n * x ≤ n * y
  mul 0 p = z≤
  mul (suc n) p = sum-mono p (mul n p)
  shift : ∀ n x → n + suc x ≡ suc (n + x)
  shift 0 x = refl
  shift (suc n) x = cong suc (shift n x)
  no : ∀ {n} → suc n ≤ n → ⊥
  no {0} ()
  no {suc n} (s≤ p) = no p
  linear : ∀ x y → (y ≤ x → ⊥) → suc x ≤ y
  linear x 0 f with f z≤
  ... | ()
  linear 0 (suc y) f = s≤ z≤
  linear (suc x) (suc y) f = s≤ (linear x y (λ p → f (s≤ p)))
  sym : ∀ {a b : Nat} → a ≡ b → b ≡ a
  sym refl = refl
  limit : ∀ w h n → h ≤ 9 → suc n ≤ w → suc (w * h + n) ≤ w * 9 + w
  limit w h n digit small rewrite sym (shift (w * h) n) = sum-mono (mul w digit) small

step : ∀ d n → suc n ≤ 131072 → suc (cshift d n) ≤ 131072
step d n small = linear (cshift d n) 131072 λ reaches →
  no (chain (limit 131072 (Digit.numeral d) n (Digit.valid d) small)
            (sound 9 (131072 * Digit.numeral d + n) 9 131072 reaches))

bounded : ∀ ds → suc (⦅ 0 ∣ cshift ⦆ ds) ≤ 131072
bounded [] = s≤ z≤
bounded (d ∷ ds) = step d _ (bounded ds)
