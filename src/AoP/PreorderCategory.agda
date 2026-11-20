{-# OPTIONS --safe --without-K #-}
module AoP.PreorderCategory where

open import AoP.Prelude
open import AoP.Categories
open import AoP.Cancellation using (module Laws′)
open import AoP.NatOrder using (_≤_; rid; chain; z≤)
open import AoP.Complement using (⊥)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (lzero)

-- Exercise 2.6. An arrow from a to b witnesses b ≤ a (the book's
-- orientation). Parallel arrows carry the same categorical information:
-- we use the indiscrete equivalence on their witnesses, so no equality
-- principle for proofs of an arbitrary preorder is required.
module Thin {A : Set} (R : A → A → Set) (reflR : ∀ a → R a a)
            (transR : ∀ {a b c} → R a b → R b c → R a c) where
  category : Category lzero lzero lzero
  category = record
    { Obj = A; Hom = λ a b → R b a; _≈_ = λ _ _ → ⊤
    ; identity = reflR _; _∘_ = transR
    ; reflexive = tt; symmetric = λ _ → tt; transitive = λ _ _ → tt
    ; compose-cong = λ _ _ → tt; unitˡ = λ _ → tt; unitʳ = λ _ → tt
    ; assoc = λ _ _ _ → tt }

  open Laws′ category
  all-monic : ∀ {a b} (f : R b a) → Monic {a} {b} f
  all-monic f x y eq = tt
  all-epic : ∀ {a b} (f : R b a) → Epic {a} {b} f
  all-epic f x y eq = tt

-- The arrow 1 → 0 exists and therefore is both monic and epic. Its
-- inverse would need an arrow 0 → 1, i.e. a witness of 1 ≤ 0.
module Natural = Thin _≤_ rid chain
forward : Category.Hom Natural.category 1 0
forward = z≤
no-return : Category.Hom Natural.category 0 1 → ⊥
no-return ()
