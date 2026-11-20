{-# OPTIONS --safe --without-K #-}
module AoP.ReserveIntervalExample where

open import AoP.Prelude
open import AoP.Reserves using (deposit; withdraw)
open import AoP.ReserveTransfer using (Executes; necessary; sufficient)
open import AoP.NatOrder using (_≤_; z≤; s≤; rid; weaken; chain)
open import Agda.Builtin.Nat using (Nat; suc; _+_)

-- §7.5. With capacity ten, which initial reserves allow +2, −5, +7
-- without a visit? A reserve r and empty space s sum to ten. The
-- extrema certificate requires r ≥ 3 and s ≥ 4, hence 3 ≤ r ≤ 6.
changes = deposit 2 ∷ withdraw 5 ∷ deposit 7 ∷ []

private
  inj : ∀ {x y} → suc x ≡ suc y → x ≡ y
  inj refl = refl
  pad : ∀ a b → b ≤ a + b
  pad 0 b = rid b
  pad (suc a) b = weaken (pad a b)
  room : ∀ r s k → r + s ≡ k + 4 → 4 ≤ s → r ≤ k
  room 0 s k eq ok = z≤
  room (suc r) s 0 eq ok with s≤ (chain ok (pad r s))
  ... | bad rewrite eq with bad
  ...   | s≤ (s≤ (s≤ (s≤ ())))
  room (suc r) s (suc k) eq ok = s≤ (room r s k (inj eq) ok)
  space : ∀ r s k → r + s ≡ k + 4 → r ≤ k → 4 ≤ s
  space 0 ._ k refl ok = pad k 4
  space (suc r) s (suc k) eq (s≤ ok) = space r s k (inj eq) ok

bounds : ∀ r s → r + s ≡ 10 → Executes changes r s → (3 ≤ r) × (r ≤ 6)
bounds r s eq run = fst (necessary run) , room r s 6 eq (snd (necessary run))

realise : ∀ r s → r + s ≡ 10 → (3 ≤ r) × (r ≤ 6) → Executes changes r s
realise r s eq (lo , hi) = sufficient changes r s (lo , space r s 6 eq hi)
