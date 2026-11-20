{-# OPTIONS --safe --without-K #-}
module AoP.EntabMinimum where

open import Agda.Builtin.Nat using (Nat; suc)
open import AoP.Prelude
open import AoP.NatOrder using (_≤_; rid; chain; s≤)
open import AoP.Snoc using (ε; _▻_)
open import AoP.Detab
open import AoP.Entab
open import AoP.TabFree
open import AoP.EntabLength
open import AoP.TabEmission
open import AoP.TabBlock

-- §10.2. Compare our encoding with ANY spelling of the same expanded
-- text. Charge one character for each pending blank as if flushing now.
-- A competitor's literal grows that charge by at most one. Its tab may
-- expand into many blanks, but processing them emits just one tab and
-- clears the pending charge. Induction now bounds the final length.
module Optimal {A : Set} (n : Nat) where
  open Expand {A} n
  open Encode {A} n
  open Image {A} n
  open Bound {A} n
  open Emission {A} n
  open Block {A} n

  charge : State → Nat
  charge (xs , k) = len (blanks xs k)

  subst≤ : ∀ {a b c} → a ≡ b → b ≤ c → a ≤ c
  subst≤ refl p = p

  tab-bound : ∀ {s} (p : Plain s) → size (encode (spaces (suc (position s)) p)) ≤ suc (size (encode p))
  tab-bound p = subst≤ (cong charge (tab-block p)) (s≤ (grows (Buffer.code (encode p)) (Buffer.pending (encode p))))

  beats : ∀ xs → size (encode (plain xs)) ≤ len xs
  beats ε = rid 0
  beats (xs ▻ blank) = chain (space-bound (encode (plain xs))) (s≤ (beats xs))
  beats (xs ▻ tab) = chain (tab-bound (plain xs)) (s≤ (beats xs))
  beats (xs ▻ newline) = s≤ (beats xs)
  beats (xs ▻ glyph a) = s≤ (beats xs)

  -- Plain has one constructor per admissible final character; its
  -- evidence cannot affect the length computed for the same text.
  unique : ∀ {s} (p q : Plain s) → p ≡ q
  unique empty empty = refl
  unique (space p) (space q) = cong space (unique p q)
  unique (line p) (line q) = cong line (unique p q)
  unique (char a p) (char .a q) = cong (char a) (unique p q)

  shortest : ∀ {s} (p : Plain s) xs → detab xs ≡ s → len (fst (entab p)) ≤ len xs
  shortest p xs refl = subst≤ (cong (λ q → size (encode q)) (unique p (plain xs))) (beats xs)
