{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.RemainderUnique where

open import AoP.Common.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import AoP.Chapter06.BinaryModulus using (module Compute)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; chain)
open import AoP.Chapter04.Complement using (⊥)

-- §2.6. Two decompositions into whole copies of a positive modulus
-- and a bounded remainder have the same remainder. Cancel one whole
-- copy on each side until one side has only its remainder left.
module Law (k : Nat) where
  open Compute k
  b = suc k
  private
    cancel : ∀ t {i j} → t + i ≡ t + j → i ≡ j
    cancel zero p = p
    cancel (suc t) p = cancel t (cong pred p)
      where pred : Nat → Nat
            pred zero = zero
            pred (suc n) = n
    lower : ∀ t n → t ≤ t + n
    lower zero n = z≤
    lower (suc t) n = s≤ (lower t n)
    impossible : ∀ t → suc t ≤ t → ⊥
    impossible zero ()
    impossible (suc t) (s≤ p) = impossible t p
    absurd : ∀ {X : Set} → ⊥ → X
    absurd ()
    large : ∀ {r n} → r ≤ k → r ≡ b + n → ⊥
    large {n = n} bound refl = impossible k (chain (lower b n) bound)
    rev : ∀ {x y : Nat} → x ≡ y → y ≡ x
    rev refl = refl
  unique : ∀ {r s i j} → r ≤ k → s ≤ k → Copies r i → Copies s j → i ≡ j → r ≡ s
  unique u v same same p = p
  unique u v same (add h) p = absurd (large u p)
  unique u v (add h) same p = absurd (large v (rev p))
  unique u v (add g) (add h) p = unique u v g h (cancel b p)

  periodic : ∀ n → fst (solve (b + n)) ≡ fst (solve n)
  periodic n with solve (b + n) | solve n
  ... | r , u , g | s , v , h = unique u v g (add h) refl
