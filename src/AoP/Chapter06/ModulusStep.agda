{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.ModulusStep where

open import AoP.Common.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _-_)
open import Agda.Builtin.Bool using (Bool)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter06.HalvingDigits using (shift)
open import AoP.Chapter06.ModulusBound using (shift-bound; reduced)

-- §6.4. At divisor b=k+1, distinguish n<b from b≤n. In the second
-- branch record that adding b back recovers n. This certificate and
-- the bound are the local arithmetic facts needed for a modulus fold.
module At (k : Nat) where
  b = suc k
  private
    compare : ∀ m n → (n ≤ m) ⊎ (suc m ≤ n)
    compare m zero = inl z≤
    compare zero (suc n) = inr (s≤ z≤)
    compare (suc m) (suc n) with compare m n
    ... | inl p = inl (s≤ p)
    ... | inr q = inr (s≤ q)

    restore : ∀ m n → m ≤ n → m + (n - m) ≡ n
    restore zero n p = refl
    restore (suc m) (suc n) (s≤ p) = cong suc (restore m n p)

  record Reduction (n : Nat) : Set where
    constructor result
    field remainder : Nat
          bounded : remainder ≤ k
          accounts : (n ≡ remainder) ⊎ (b + remainder ≡ n)

  reduce : ∀ n → n ≤ suc (AoP.Chapter06.HalvingDigits.double k) → Reduction n
  reduce n bound with compare k n
  ... | inl small = result n small (inl refl)
  ... | inr large = result (n - b) (reduced k n bound) (inr (restore b n large))

  update : ∀ bit r → r ≤ k → Reduction (shift bit r)
  update bit r old-bound = reduce (shift bit r) (shift-bound bit old-bound)
