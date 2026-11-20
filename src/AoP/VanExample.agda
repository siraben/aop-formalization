{-# OPTIONS --safe --without-K #-}
module AoP.VanExample where

open import AoP.Prelude
open import AoP.Reserves
open import AoP.VanSchedule
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)

-- How often must a van come when the vault can hold ten units? The
-- starting balance for each block is free to choose; only the boundaries
-- between blocks count. Read out the count from the certified solution,
-- not from a hand-written partition. `nothing` is distinct from zero.
open Schedule 10

answer : (t : Tx) (ts : List Tx) → Maybe Nat
answer t ts with solve t ts
... | impossible _ = nothing
... | optimal plan _ _ _ = just (visits plan)

-- Start at three: the balances 5, 0, and 7 all fit.
no-visit : answer (deposit 2) (withdraw 5 ∷ deposit 7 ∷ []) ≡ just 0
no-visit = refl

-- Each deposit fits alone, but two adjacent deposits of six cannot fit
-- even from zero. A visit is necessary after each of the first two.
two-visits : answer (deposit 6) (deposit 6 ∷ deposit 6 ∷ []) ≡ just 2
two-visits = refl

-- No number of visits can make a single deposit of eleven fit.
infeasible : answer (deposit 11) [] ≡ nothing
infeasible = refl

open import AoP.VanRefinement using (module Refine)
open import AoP.Paragraph using (_∷⁺_)

-- Three deposits of four require one visit. Either gap works; the
-- longest-prefix rule chooses the second gap, after the vault reaches
-- eight from zero. Resetting to zero then permits the last deposit.
chosen : (t : Tx) (ts : List Tx) → Maybe Plan
chosen t ts with Refine.greedy 10 t ts
... | impossible _ = nothing
... | optimal plan _ _ _ = just plan

latest-visit : chosen (deposit 4) (deposit 4 ∷ deposit 4 ∷ []) ≡
  just ((deposit 4 ∷⁺ (deposit 4 ∷ [])) ∷⁺ ((deposit 4 ∷⁺ []) ∷ []))
latest-visit = refl
