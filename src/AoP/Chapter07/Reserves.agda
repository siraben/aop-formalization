{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.Reserves where

open import AoP.Common.Prelude
open import Agda.Builtin.Nat using (Nat; _+_)
open import AoP.Common.NatOrder using (_≤_)

-- §7.5 — When can a bank process a block of transactions without a van
-- visit? The van may choose the starting balance, but every intermediate
-- balance must lie between zero and the bank's capacity. With capacity
-- ten, a deposit of two, withdrawal of five, and deposit of seven works
-- from reserve three: the balances are 3, 5, 0, 7. A final balance in
-- range would not suffice if the account went negative along the way.
data Tx : Set where
  deposit withdraw : Nat → Tx

-- Natural balances enforce nonnegativity. In the withdrawal constructor
-- the old balance must actually equal amount + new balance: truncated
-- subtraction would incorrectly permit withdrawing from an empty account.
data Changes : Tx → Nat → Nat → Set where
  credit : ∀ n r → Changes (deposit n) r (n + r)
  debit : ∀ n r → Changes (withdraw n) (n + r) r

module Bank (capacity : Nat) where
  data Run : List Tx → Nat → Nat → Set where
    stop : ∀ {r} → r ≤ capacity → Run [] r r
    post : ∀ {t ts a b c} → a ≤ capacity → Changes t a b → Run ts b c → Run (t ∷ ts) a c

  Secure : List Tx → Set
  Secure ts = Σ Nat λ a → Σ Nat λ b → Run ts a b

  -- Cutting a run at a van visit exposes its actual intermediate balance.
  -- Thus every prefix and suffix of a secure block is itself secure.
  open import AoP.Chapter01.Naturality using (_++_)
  cut : ∀ xs ys {a c} → Run (xs ++ ys) a c → Σ Nat λ b → Run xs a b × Run ys b c
  cut [] ys (stop fits) = _ , stop fits , stop fits
  cut [] ys (post fits t p) = _ , stop fits , post fits t p
  cut (x ∷ xs) ys (post fits t p) with cut xs ys p
  ... | b , l , r = b , post fits t l , r

  join : ∀ {xs ys a b c} → Run xs a b → Run ys b c → Run (xs ++ ys) a c
  join (stop _) q = q
  join (post fits t p) q = post fits t (join p q)
