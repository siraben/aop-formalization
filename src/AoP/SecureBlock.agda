{-# OPTIONS --safe --without-K #-}
module AoP.SecureBlock where

open import AoP.Prelude
open import AoP.Reserves
open import AoP.Complement using (⊥)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.ParagraphMinimum using (Dec; le?)
open import AoP.NatOrder using (_≤_; z≤; s≤; rid; weaken)
open import Agda.Builtin.Nat using (Nat; zero; suc)

-- §7.5. A capacity bound makes the possible starting reserves finite.
-- Test every reserve in [0,N]; for each one there is at most one way to
-- execute the block. A positive result contains the intermediate balances;
-- a negative one refutes every feasible run, not merely the last attempt.
module Check (cap : Nat) where
  open Bank cap

  -- Cancelling one unit from both the requested withdrawal and the
  -- current reserve preserves the possible final balance.
  lift : ∀ n a b → Changes (withdraw n) a b → Changes (withdraw (suc n)) (suc a) b
  lift n _ b (debit .n .b) = debit (suc n) b
  lower : ∀ n a b → Changes (withdraw (suc n)) (suc a) b → Changes (withdraw n) a b
  lower n _ b (debit .(suc n) .b) = debit n b

  next : ∀ t a → Dec (Σ Nat λ b → Changes t a b)
  next (deposit n) a = inl (_ , credit n a)
  next (withdraw zero) a = inl (a , debit 0 a)
  next (withdraw (suc n)) zero = inr λ { (_ , ()) }
  next (withdraw (suc n)) (suc a) with next (withdraw n) a
  ... | inl (b , p) = inl (b , lift n a b p)
  ... | inr no = inr λ { (b , p) → no (b , lower n a b p) }

  cancel+ : ∀ n {a b} → Agda.Builtin.Nat._+_ n a ≡ Agda.Builtin.Nat._+_ n b → a ≡ b
  cancel+ zero eq = eq
  cancel+ (suc n) eq = cancel+ n (cong pred eq)
    where pred : Nat → Nat
          pred zero = zero
          pred (suc m) = m

  deterministic : ∀ {t a b c} → Changes t a b → Changes t a c → b ≡ c
  deterministic (credit n a) (credit .n .a) = refl
  deterministic {b = b} {c} (debit n .b) q = recover n c q refl
    where
    recover : ∀ n c {a} → Changes (withdraw n) a c → a ≡ Agda.Builtin.Nat._+_ n b → b ≡ c
    recover n c (debit .n .c) eq with cancel+ n eq
    ... | refl = refl

  from : ∀ ts a → Dec (Σ Nat λ b → Run ts a b)
  from [] a with le? a cap
  ... | inl ok = inl (a , stop ok)
  ... | inr no = inr λ { (_ , stop ok) → no ok }
  from (t ∷ ts) a with le? a cap | next t a
  ... | inr no | _ = inr λ { (_ , post ok _ _) → no ok }
  ... | _ | inr no = inr λ { (_ , post _ move _) → no (_ , move) }
  ... | inl ok | inl (b , move) with from ts b
  ...   | inl (c , tail) = inl (c , post ok move tail)
  ...   | inr no = inr λ { (c , post _ move′ tail) → reject no move′ tail }
    where
    reject : ∀ {b′ c} → (Σ Nat (Run ts b) → ⊥) → Changes t a b′ → Run ts b′ c → ⊥
    reject no p tail with deterministic move p
    ... | refl = no (_ , tail)

  -- `search n` considers reserve zero through n inclusive. Comparing
  -- the *index* with n lets the negative branch exclude every witness.
  module Starts (ts : List Tx) where
    Works : Nat → Set
    Works a = Σ Nat (Run ts a)
    Within : Nat → Set
    Within n = Σ Nat λ a → (a ≤ n) × Works a

    boundary : ∀ a n → a ≤ suc n → (a ≡ suc n) ⊎ (a ≤ n)
    boundary zero n b = inr z≤
    boundary (suc _) zero (s≤ z≤) = inl refl
    boundary (suc a) (suc n) (s≤ b) with boundary a n b
    ... | inl eq = inl (cong suc eq)
    ... | inr le = inr (s≤ le)

    search : ∀ n → Dec (Within n)
    search zero with from ts 0
    ... | inl w = inl (0 , z≤ , w)
    ... | inr no = inr λ { (zero , z≤ , w) → no w }
    search (suc n) with from ts (suc n) | search n
    ... | inl w | _ = inl (suc n , rid _ , w)
    ... | inr _ | inl (a , le , w) = inl (a , weaken le , w)
    ... | inr last | inr prev = inr reject
      where
      reject : Within (suc n) → ⊥
      reject (a , le , w) with boundary a n le
      ... | inl refl = last w
      ... | inr small = prev (a , small , w)

  initial : ∀ {ts a b} → Run ts a b → a ≤ cap
  initial (stop ok) = ok
  initial (post ok _ _) = ok

  secure? : ∀ ts → Dec (Secure ts)
  secure? ts with Starts.search ts cap
  ... | inl (a , _ , w) = inl (a , w)
  ... | inr no = inr λ { (a , b , run) → no (a , initial run , b , run) }
