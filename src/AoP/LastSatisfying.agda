{-# OPTIONS --safe --without-K #-}
module AoP.LastSatisfying where

open import AoP.Prelude
open import AoP.Naturals using (foldn)
open import AoP.NatOrder using (_≤_; z≤; s≤; rid; weaken)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (Bool; true; false)

-- Exercise 1.5. Scan [0,n] and remember the most recent passing index.
-- This also answers the strict-bound query for indices below suc n.
-- The hypothesis at zero supplies an answer for the first interval.
module Scan (p : Nat → Bool) (initial : p 0 ≡ true) where
  step : Nat × Nat → Nat × Nat
  step (n , k) with p (suc n)
  ... | true = suc n , suc n
  ... | false = suc n , k

  state : Nat → Nat × Nat
  state = foldn (0 , 0) step

  record Best (n k : Nat) : Set where
    constructor best
    field within : k ≤ n
          passes : p k ≡ true
          greatest : ∀ m → m ≤ n → p m ≡ true → m ≤ k

  -- Any index within the enlarged interval is either old or its new end.
  open import AoP.Polynomial using (_⊎_; inl; inr)
  endpoint : ∀ m n → m ≤ suc n → (m ≤ n) ⊎ (m ≡ suc n)
  endpoint zero n _ = inl z≤
  endpoint (suc m) zero (s≤ z≤) = inr refl
  endpoint (suc m) (suc n) (s≤ le) with endpoint m n le
  ... | inl old = inl (s≤ old)
  ... | inr eq = inr (cong suc eq)

  invariant : ∀ n → (fst (state n) ≡ n) × Best n (snd (state n))
  invariant zero = refl , best z≤ initial (λ _ le _ → le)
  invariant (suc n) with state n | invariant n
  ... | .n , k | refl , best le ok greatest with p (suc n) in tested
  ...   | true = refl , best (rid _) tested (λ _ b _ → b)
  ...   | false = refl , best (weaken le) ok bound
    where
    bound : ∀ m → m ≤ suc n → p m ≡ true → m ≤ k
    bound m b pass with endpoint m n b
    ... | inl old = greatest m old pass
    ... | inr refl = clash tested pass
      where
      clash : ∀ {b : Bool} {X : Set} → b ≡ false → b ≡ true → X
      clash refl ()

  last : Nat → Nat
  last n = snd (state n)

  correct : ∀ n → Best n (last n)
  correct n = snd (invariant n)
