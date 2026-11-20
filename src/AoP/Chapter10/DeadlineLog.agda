{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.DeadlineLog where

open import AoP.Common.Prelude
open import AoP.Chapter10.DeadlineRunCount using (double; power)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; rid; weaken; chain)
open import AoP.Chapter08.ParagraphMinimum using (le?)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Chapter04.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat; suc)

-- Choose the least number of merge rounds whose capacity covers n.
-- Incrementing n crosses at most one power-of-two boundary. This gives
-- ceil(log₂ n) on positive inputs and the convention zero rounds at 0.
private
  room : ∀ x → x ≤ double x
  room 0 = z≤
  room (suc x) = s≤ (weaken (room x))
  positive : ∀ k → 1 ≤ power k
  positive 0 = rid 1
  positive (suc k) = chain (positive k) (room (power k))
  extra : ∀ x → 1 ≤ x → suc x ≤ double x
  extra (suc x) _ = s≤ (s≤ (room x))
  monotone : ∀ {i j} → i ≤ j → power i ≤ power j
  monotone {j = j} z≤ = positive j
  monotone (s≤ le) = twice (monotone le)
    where twice : ∀ {a b} → a ≤ b → double a ≤ double b
          twice z≤ = z≤
          twice (s≤ p) = s≤ (s≤ (twice p))
  strict : ∀ {i j} → i ≤ j → (j ≤ i → ⊥) → suc i ≤ j
  strict {j = 0} z≤ no with no z≤
  ... | ()
  strict {j = suc j} z≤ no = s≤ z≤
  strict (s≤ p) no = s≤ (strict p (λ q → no (s≤ q)))

record Budget (n : Nat) : Set where
  constructor budget
  field rounds : Nat
        fits : n ≤ power rounds
        least : ∀ j → n ≤ power j → rounds ≤ j

choose : ∀ n → Budget n
choose 0 = budget 0 z≤ (λ _ _ → z≤)
choose (suc n) with choose n
... | budget k b least with le? (suc n) (power k)
...   | inl ok = budget k ok (λ j p → least j (chain (weaken (rid n)) p))
...   | inr no = budget (suc k) (chain (s≤ b) (extra (power k) (positive k))) λ j p →
      strict (least j (chain (weaken (rid n)) p)) (λ le → no (chain p (monotone le)))

five : Budget.rounds (choose 5) ≡ 3
five = refl
