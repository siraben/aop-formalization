{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.CompressionGrowth where

open import AoP.Common.Prelude
open import AoP.Chapter09.Compression using (module Text)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; rid; chain; weaken)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Maybe using (just; nothing)

-- §9.4. To search for a cheapest encoding, first bound the search by
-- the length of the target. Every successful instruction adds at least
-- one letter, including a pointer whose source overlaps its destination.
len : ∀ {A : Set} → List A → Nat
len [] = zero
len (_ ∷ xs) = suc (len xs)

module Bound {A : Set} where
  open Text {A}

  push : ∀ (xs : List A) x → len (xs ++ (x ∷ [])) ≡ suc (len xs)
  push [] x = refl
  push (y ∷ ys) x = cong suc (push ys x)

  -- Track both output size and remaining instruction budget using
  -- iteration; spending one token increments the lower bound by one.
  grow : Nat → Nat → Nat
  grow zero n = n
  grow (suc k) n = grow k (suc n)

  mono : ∀ k {a b} → a ≤ b → grow k a ≤ grow k b
  mono zero le = le
  mono (suc k) le = mono k (s≤ le)

  extends : ∀ k n → n ≤ grow k n
  extends zero n = rid n
  extends (suc k) n = chain (weaken (rid n)) (extends k (suc n))

  copied : ∀ i k xs {ys} → copy i k xs ≡ just ys → len ys ≡ grow k (len xs)
  copied i zero xs refl = refl
  copied i (suc k) xs eq with lookup i xs
  ... | nothing with eq
  ...   | ()
  copied i (suc k) xs eq | just x = begin
    _ ≡⟨ copied (suc i) k (xs ++ (x ∷ [])) eq ⟩
    grow k (len (xs ++ (x ∷ []))) ≡⟨ cong (grow k) (push xs x) ⟩
    grow k (suc (len xs)) ∎

  bound : ∀ ops xs {ys} → run xs ops ≡ just ys → grow (len ops) (len xs) ≤ len ys
  bound [] xs refl = rid _
  bound (sym x ∷ ops) xs eq with bound ops (xs ++ (x ∷ [])) eq
  ... | le rewrite push xs x = le
  bound (ptr i k ∷ ops) xs eq with copy i (suc k) xs in c
  ... | nothing with eq
  ...   | ()
  bound (ptr i k ∷ ops) xs eq | just zs with bound ops zs eq | copied i (suc k) xs c
  ... | le | size rewrite size = chain (mono (len ops) (extends k (suc (len xs)))) le
