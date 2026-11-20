{-# OPTIONS --safe --without-K #-}
module AoP.FillPrefixes where

open import AoP.Prelude
open import AoP.Snoc using (Snoc; ε; _▻_)
open import AoP.Detab
open import Agda.Builtin.Nat using (Nat)
open import AoP.Complement using (⊥)
open import AoP.Polynomial using (_⊎_; inl; inr)

-- Exercise 10.4. Prefixes are obtained by removing zero or more
-- trailing characters. V additionally requires that filling to the
-- next tab stop yields exactly the same text.
data Prefix {A : Set} (x : Snoc A) : Snoc A → Set where
  same : Prefix x x
  drop : ∀ {y} a → Prefix x y → Prefix x (y ▻ a)

nil-law : ∀ {A : Set} {x : Snoc A} → Prefix x ε → x ≡ ε
nil-law same = refl

snoc-law : ∀ {A : Set} {x y : Snoc A} {a} → Prefix x (y ▻ a) → (x ≡ (y ▻ a)) ⊎ Prefix x y
snoc-law same = inl refl
snoc-law (drop a p) = inr p

module Restricted {A : Set} (n : Nat) where
  open Expand {A} n
  fill : Text → Text
  fill xs = expand xs tab
  V : Text → Text → Set
  V x y = Prefix x y × (fill x ≡ fill y)
  nil-out : ∀ {x} → V x ε → x ≡ ε
  nil-out (p , _) = nil-law p
  nil-in : V ε ε
  nil-in = same , refl

-- At width one filling the empty text gives one blank, whose empty
-- prefix differs from the filled text. Thus prefix ∘ fill = fill fails.
module Failure {A : Set} where
  open Restricted {A} 0
  witness : Prefix ε (fill ε)
  witness = drop blank same
  distinct : ε ≡ fill ε → ⊥
  distinct ()
