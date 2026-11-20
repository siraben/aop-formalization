{-# OPTIONS --safe --without-K #-}
module AoP.TardinessBound where

open import Agda.Builtin.Nat using (Nat; zero; suc; _-_; _*_)
open import AoP.NatOrder using (_≤_; z≤; s≤; rid; sum-mono; chain)
open import AoP.Tardiness using (Job)
open Job using (due; duration; weight)
open import AoP.ScheduleExchange using (module Law)

-- §10.3. Instantiate the exchange law with the actual weighted tardiness
-- objective. The time here is *completion* time: do not add duration
-- again. Natural subtraction clamps early completion to a zero penalty.
charge : Job → Nat → Nat
charge j t = (t - due j) * weight j

private
  pred-mono : ∀ {a b} → suc a ≤ suc b → a ≤ b
  pred-mono (s≤ le) = le

  subtract-mono : ∀ {a b} d → a ≤ b → (a - d) ≤ (b - d)
  subtract-mono zero le = le
  subtract-mono {zero} (suc d) le = z≤
  subtract-mono {suc a} {suc b} (suc d) le = subtract-mono d (pred-mono le)

  scale-mono : ∀ {a b} w → a ≤ b → (a * w) ≤ (b * w)
  scale-mono w z≤ = z≤
  scale-mono w (s≤ le) = sum-mono (rid w) (scale-mono w le)

charge-mono : ∀ j {a b} → a ≤ b → charge j a ≤ charge j b
charge-mono j le = scale-mono (weight j) (subtract-mono (due j) le)

-- For a candidate bound k, every job has to finish with penalty ≤ k.
-- Moving a job last is now certified whenever *its* final penalty fits;
-- all intervening jobs keep the bound without a separate test.
module Limit (k : Nat) where
  Allowed : Job → Nat → Set
  Allowed j t = charge j t ≤ k

  open Law duration Allowed (λ j le ok → chain (charge-mono j le) ok) public
