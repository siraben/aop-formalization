{-# OPTIONS --safe --without-K #-}
module AoP.ReserveTransfer where

open import AoP.Prelude
open import AoP.Reserves using (Tx; deposit; withdraw)
open import AoP.ReserveExtrema
open import AoP.NatOrder using (_≤_; z≤; s≤; rid; sum-mono)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

-- Treat stock and empty vault space as two accounts. A transaction
-- transfers units between them. Writing the source as n + remainder
-- ensures that neither account can go negative.
data Executes : List Tx → Nat → Nat → Set where
  stop : ∀ {r s} → Executes [] r s
  credit : ∀ n r s {ts} → Executes ts (n + r) s → Executes (deposit n ∷ ts) r (n + s)
  debit : ∀ n r s {ts} → Executes ts r (n + s) → Executes (withdraw n ∷ ts) (n + r) s

necessary : ∀ {ts r s} → Executes ts r s → Fits (summary ts) r s
necessary stop = z≤ , z≤
necessary (credit n r s {ts} p) = credit-out n (summary ts) r s (necessary p)
necessary (debit n r s {ts} p) = debit-out n (summary ts) r s (necessary p)

-- Split off the transferred amount, retaining the lower bound on the
-- remainder. This constructive decomposition determines the next state.
split : ∀ n {a b} → (n + a) ≤ b → Σ Nat λ d → (b ≡ n + d) × (a ≤ d)
split zero {b = b} p = b , refl , p
split (suc n) (s≤ p) with split n p
... | d , refl , q = d , refl , q

sufficient : ∀ ts r s → Fits (summary ts) r s → Executes ts r s
sufficient [] r s _ = stop
sufficient (deposit n ∷ ts) r s (lp , hp) with split n hp
... | d , refl , q = credit n r d (sufficient ts (n + r) d (shift _ n r lp , q))
sufficient (withdraw n ∷ ts) r s (lp , hp) with split n lp
... | d , refl , q = debit n d s (sufficient ts d (n + s) (q , shift _ n s hp))

-- The minimum feasible total vault capacity is attained by starting with
-- exactly the two extrema. Any successful run has at least this capacity.
minimum-capacity : ∀ ts → Nat
minimum-capacity ts = Needs.stock (summary ts) + Needs.space (summary ts)

attained : ∀ ts → Executes ts (Needs.stock (summary ts)) (Needs.space (summary ts))
attained ts = sufficient ts _ _ (rid _ , rid _)

least : ∀ {ts r s} → Executes ts r s → minimum-capacity ts ≤ r + s
least p = sum-mono (fst (necessary p)) (snd (necessary p))
