{-# OPTIONS --safe --without-K #-}
module AoP.TabCountdown where

open import Agda.Builtin.Nat using (Nat; zero; suc; _-_)
open import AoP.Prelude
open import AoP.NatOrder using (_≤_; z≤; s≤)
open import AoP.Complement using (⊥)

-- The buffered encoder tests a counter against the next stop. Once
-- pending = stop it emits a tab on the *next* blank. Thus exactly
-- 1 + (stop − pending) blanks are needed to trigger emission. Prove
-- this independently of the output text: arbitrary state types may
-- instantiate wait (consume one blank) and emit (return the new state).
module Count where

  data Gap : Nat → Nat → Nat → Set where
    equal : ∀ k → Gap k k 0
    before : ∀ {k m d} → Gap (suc k) m d → Gap k m (suc d)

  shift : ∀ {k m d} → Gap k m d → Gap (suc k) (suc m) d
  shift (equal k) = equal (suc k)
  shift (before g) = before (shift g)

  from-zero : ∀ m → Gap 0 m m
  from-zero zero = equal 0
  from-zero (suc m) = before (shift (from-zero m))

  countdown : ∀ {k m} → k ≤ m → Gap k m (m - k)
  countdown {zero} {m} z≤ = from-zero m
  countdown (s≤ le) = shift (countdown le)

  below : ∀ {k m d} → Gap k m d → k ≤ m
  below (equal k) = id≤ k
    where id≤ : ∀ k → k ≤ k
          id≤ zero = z≤
          id≤ (suc k) = s≤ (id≤ k)
  below (before g) = drop (below g)
    where drop : ∀ {a b} → suc a ≤ b → a ≤ b
          drop {zero} _ = z≤
          drop {suc a} (s≤ p) = s≤ (drop p)

  irreflexive : ∀ k → suc k ≤ k → ⊥
  irreflexive zero ()
  irreflexive (suc k) (s≤ p) = irreflexive k p

  module Trace {S : Set} (tick : S → S) (waiting : Nat → S) (emitted : S) (m : Nat)
               (at : tick (waiting m) ≡ emitted)
               (early : ∀ k → suc k ≤ m → tick (waiting k) ≡ waiting (suc k)) where
    ticks : Nat → S → S
    ticks zero s = s
    ticks (suc d) s = ticks d (tick s)

    trigger : ∀ {k d} → Gap k m d → ticks (suc d) (waiting k) ≡ emitted
    trigger (equal k) = at
    trigger (before {k} {d = d} g) = begin
      ticks (suc d) (tick (waiting k))
        ≡⟨ cong (ticks (suc d)) (early k (below g)) ⟩
      ticks (suc d) (waiting (suc k))
        ≡⟨ trigger g ⟩
      emitted ∎
