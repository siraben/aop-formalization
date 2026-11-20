{-# OPTIONS --safe --without-K #-}
module AoP.DictionaryCachedSize where

open import AoP.Prelude
open import AoP.Compression using (module Text)
open import AoP.DictionarySplice using (module Splice)
open import AoP.Naturality using (_++_)
open import AoP.NatOrder using (_≤_; rid)
open import Agda.Builtin.Nat using (Nat; _+_)

-- §9.4's paired representation. Maintain the size when snoccing one
-- instruction; a comparison can then read both costs from the pairs.
module Cache {A : Set} (c p : Nat) where
  open Text {A}
  open Splice {A} c p using (price; append-cost)
  record Entry : Set where
    constructor entry
    field program : List Code
          size : Nat
          exact : size ≡ price program
  open Entry
  empty : Entry
  empty = entry [] 0 refl
  charge : Code → Nat
  charge (sym _) = c
  charge (ptr _ _) = p
  private
    unit : ∀ n → n + 0 ≡ n
    unit 0 = refl
    unit (Agda.Builtin.Nat.suc n) = cong Agda.Builtin.Nat.suc (unit n)
    reverse : ∀ {x y : Nat} → x ≡ y → y ≡ x
    reverse refl = refl
  singleton : ∀ op → price (op ∷ []) ≡ charge op
  singleton (sym _) = unit c
  singleton (ptr _ _) = unit p
  push : Entry → Code → Entry
  push (entry ps n eq) op = entry (ps ++ (op ∷ [])) (n + charge op) (begin
    n + charge op ≡⟨ cong (_+ charge op) eq ⟩
    price ps + charge op ≡⟨ cong (price ps +_) (reverse (singleton op)) ⟩
    price ps + price (op ∷ []) ≡⟨ reverse (append-cost ps (op ∷ [])) ⟩
    price (ps ++ (op ∷ [])) ∎)
  compare-cost : ∀ u v → size u ≤ size v → price (program u) ≤ price (program v)
  compare-cost (entry _ _ refl) (entry _ _ refl) le = le
