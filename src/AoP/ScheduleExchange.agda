{-# OPTIONS --safe --without-K #-}
module AoP.ScheduleExchange where

open import AoP.Prelude
open import AoP.Permutations using (Insert; front; later)
open import AoP.NatOrder using (_≤_; rid; sum-mono; chain; z≤)
open import Agda.Builtin.Nat using (Nat; _+_)

-- §10.3. To put a chosen job last, remove its old occurrence and slide
-- intervening jobs earlier. Why can't that make them miss a penalty
-- bound? Each such job finishes no later, and admissibility is closed
-- under earlier finish times. We isolate this exchange argument from
-- the arithmetic formula for weighted tardiness.
module Law {Job : Set} (duration : Job → Nat) (Allowed : Job → Nat → Set)
           (earlier : ∀ j {s t} → s ≤ t → Allowed j t → Allowed j s) where
  -- `Fits s js` means the jobs, run sequentially starting at s, all
  -- satisfy their respective bound at completion, not at start time.
  data Fits : Nat → List Job → Set where
    empty : ∀ {s} → Fits s []
    step : ∀ {s j js} → Allowed j (s + duration j) → Fits (s + duration j) js → Fits s (j ∷ js)

  advance : ∀ {s t js} → s ≤ t → Fits t js → Fits s js
  advance le empty = empty
  advance le (step {j = j} ok tail) = step (earlier j le′ ok) (advance le′ tail)
    where le′ = sum-mono le (rid (duration j))

  opens-slot : ∀ {j xs ys s} → Insert j xs ys → Fits s ys → Fits s xs
  opens-slot {j} {s = s} front (step ok tail) = advance (delay s (duration j)) tail
    where
    delay : ∀ a b → a ≤ a + b
    delay 0 b = z≤
    delay (Agda.Builtin.Nat.suc a) b = AoP.NatOrder.s≤ (delay a b)
  opens-slot (later i) (step ok tail) = step ok (opens-slot i tail)

  -- Finish time of a prefix, evaluated in execution order.
  finish : Nat → List Job → Nat
  finish s [] = s
  finish s (j ∷ js) = finish (s + duration j) js

  append : List Job → Job → List Job
  append [] j = j ∷ []
  append (x ∷ xs) j = x ∷ append xs j

  append-last : ∀ {s xs} j → Fits s xs → Allowed j (finish s xs + duration j) →
                Fits s (append xs j)
  append-last j empty ok = step ok empty
  append-last j (step ok tail) last = step ok (append-last j tail last)

  exchange : ∀ {s xs ys} j → Insert j xs ys → Fits s ys →
             Allowed j (finish s xs + duration j) → Fits s (append xs j)
  exchange j i run ok = append-last j (opens-slot i run) ok
