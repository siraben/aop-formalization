{-# OPTIONS --safe --without-K #-}
module AoP.PositiveFold where

open import AoP.Prelude
open import AoP.Complement using (⊥)
open import AoP.Naturals using (foldn)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- Exercise 1.1. The recursion equation f n = suc (f n) has no
-- natural-valued solution: already its instance at zero is impossible.
no-successor-loop : ∀ n → n ≡ suc n → ⊥
no-successor-loop zero ()
no-successor-loop (suc n) eq = no-successor-loop n (cong pred eq)
  where pred : Nat → Nat
        pred zero = zero
        pred (suc k) = k

no-solution : (f : Nat → Nat) → (∀ n → f n ≡ suc (f n)) → ⊥
no-solution f law = no-successor-loop (f zero) (law zero)

-- Exercise 1.3. Count successors from one instead of zero. For example
-- three has two successor steps in this representation; the inverse map
-- reads the number of steps, so three corresponds to the natural two.
data Positive : Set where
  one : Positive
  next : Positive → Positive

fold⁺ : ∀ {A : Set} → A → (A → A) → Positive → A
fold⁺ base step one = base
fold⁺ base step (next p) = step (fold⁺ base step p)

encode : Nat → Positive
encode = foldn one next

decode : Positive → Nat
decode = fold⁺ zero suc

round-nat : ∀ n → decode (encode n) ≡ n
round-nat zero = refl
round-nat (suc n) = cong suc (round-nat n)

round-positive : ∀ p → encode (decode p) ≡ p
round-positive one = refl
round-positive (next p) = cong next (round-positive p)

-- Transporting a positive fold across the correspondence recovers the
-- ordinary natural fold with the same starting value and step.
transport : ∀ {A : Set} (base : A) step n → fold⁺ base step (encode n) ≡ foldn base step n
transport base step zero = refl
transport base step (suc n) = cong step (transport base step n)
