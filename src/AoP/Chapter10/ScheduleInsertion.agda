{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.ScheduleInsertion where

open import AoP.Common.Prelude
open import AoP.Chapter01.Snoc using (Snoc; _▻_)
open import AoP.Chapter10.Tardiness using (Job; elapsed; cost; penalty)
open import AoP.Chapter10.TardinessBound using (charge-mono)
open import AoP.Chapter01.Trees using (max)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; rid; weaken; sum-mono)
open import Agda.Builtin.Nat using (Nat; suc; _+_)

-- Exercise 10.7. The constructors generate the least relation closed
-- under appending the new job and inserting it before an old last job.
data Add (j : Job) : Snoc Job → Snoc Job → Set where
  last : ∀ {xs} → Add j xs (xs ▻ j)
  before : ∀ {xs ys} k → Add j xs ys → Add j (xs ▻ k) (ys ▻ k)

induct : ∀ {P : Snoc Job → Snoc Job → Set} {j} →
         (∀ xs → P xs (xs ▻ j)) → (∀ {xs ys} k → P xs ys → P (xs ▻ k) (ys ▻ k)) →
         ∀ {xs ys} → Add j xs ys → P xs ys
induct base step last = base _
induct {P} base step (before {xs} {ys} k i) = step {xs} {ys} k (induct {P} base (λ {u} {v} → step {u} {v}) i)

private
  delay : ∀ t d → t ≤ t + d
  delay 0 d = z≤
  delay (suc t) d = s≤ (delay t d)
  left : ∀ a b → a ≤ max a b
  left 0 b = z≤
  left (suc a) 0 = rid _
  left (suc a) (suc b) = s≤ (left a b)
  mono : ∀ {a b c d} → a ≤ b → c ≤ d → max a c ≤ max b d
  mono {b = b} z≤ q = right b q
    where right : ∀ b {c d} → c ≤ d → c ≤ max b d
          right 0 q = q
          right (suc b) z≤ = z≤
          right (suc b) (s≤ q) = s≤ (right b q)
  mono {c = 0} {d} (s≤ p) z≤ = left′ _ d p
    where left′ : ∀ b d {a} → a ≤ b → suc a ≤ max (suc b) d
          left′ b 0 p = s≤ p
          left′ b (suc d) p = s≤ (AoP.Common.NatOrder.chain p (left b d))
  mono (s≤ p) (s≤ q) = s≤ (mono p q)

-- Strengthen the prefixpoint with elapsed time. This supplies exactly
-- the comparison of the two penalties when the old last job is restored.
Invariant : Snoc Job → Snoc Job → Set
Invariant xs ys = (elapsed xs ≤ elapsed ys) × (cost xs ≤ cost ys)

monotone : ∀ {j xs ys} → Add j xs ys → Invariant xs ys
monotone {j} = induct {P = Invariant} (λ xs → delay (elapsed xs) (Job.duration j) , left (cost xs) (penalty (elapsed xs) j)) (λ {u} {v} → step {u} {v})
  where step : ∀ {xs ys} k → Invariant xs ys → Invariant (xs ▻ k) (ys ▻ k)
        step {xs} {ys} k (time , peak) = let t = sum-mono time (rid (Job.duration k)) in
          t , mono peak (charge-mono k t)
