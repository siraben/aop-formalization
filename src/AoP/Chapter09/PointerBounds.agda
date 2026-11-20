{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.PointerBounds where

open import AoP.Common.Prelude
open import AoP.Chapter09.Compression using (module Text)
open import AoP.Chapter09.CompressionGrowth using (len; module Bound)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Common.NatOrder using (_≤_; z≤; s≤; rid; chain; weaken)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Maybe using (just; nothing)

-- §9.4. A finite search also needs bounds on the two integers inside
-- every pointer. Its first lookup is in the *old* prefix. Later lookups
-- may overlap the newly appended text, so bounding the whole source by
-- the old prefix would be too strong. Bound the length by the final text.
module Bounds {A : Set} where
  open Text {A}
  open Bound {A}

  index : ∀ i xs {x} → lookup i xs ≡ just x → suc i ≤ len xs
  index i [] ()
  index zero (_ ∷ _) eq = s≤ z≤
  index (suc i) (_ ∷ xs) eq = s≤ (index i xs eq)

  first-lookup : ∀ i k xs {ys} → copy i (suc k) xs ≡ just ys → suc i ≤ len xs
  first-lookup i k xs eq with lookup i xs in searched
  ... | just x = index i xs searched
  ... | nothing with eq
  ...   | ()

  -- Iterating successor commutes with one additional successor.
  grow-suc : ∀ k n → grow k (suc n) ≡ suc (grow k n)
  grow-suc zero n = refl
  grow-suc (suc k) n = grow-suc k (suc n)

  count-bound : ∀ k n → k ≤ grow k n
  count-bound zero n = z≤
  count-bound (suc k) n rewrite grow-suc k n = s≤ (count-bound k n)

  size-bound : ∀ i k xs {ys} → copy i k xs ≡ just ys → k ≤ len ys
  size-bound i k xs eq rewrite copied i k xs eq = count-bound k (len xs)

  -- Each successful suffix extends its starting text. This lifts the
  -- local bounds to a single global bound for the entire code stream.
  prefix-bound : ∀ ops xs {ys} → run xs ops ≡ just ys → len xs ≤ len ys
  prefix-bound ops xs eq = chain (extends (len ops) (len xs)) (bound ops xs eq)

  data Bounded (N : Nat) : List Code → Set where
    end : Bounded N []
    literal : ∀ {a ops} → Bounded N ops → Bounded N (sym a ∷ ops)
    pointer : ∀ {i k ops} → suc i ≤ N → suc k ≤ N → Bounded N ops → Bounded N (ptr i k ∷ ops)

  all-bounded : ∀ ops xs {ys} → run xs ops ≡ just ys → Bounded (len ys) ops
  all-bounded [] xs eq = end
  all-bounded (sym a ∷ ops) xs eq = literal (all-bounded ops (xs ++ (a ∷ [])) eq)
  all-bounded (ptr i k ∷ ops) xs eq with copy i (suc k) xs in cp
  ... | nothing with eq
  ...   | ()
  all-bounded (ptr i k ∷ ops) xs eq | just zs =
    pointer (chain (first-lookup i k xs cp) (chain grows rest))
            (chain (size-bound i (suc k) xs cp) rest) (all-bounded ops zs eq)
    where
    grows : len xs ≤ len zs
    grows rewrite copied i (suc k) xs cp = extends (suc k) (len xs)
    rest = prefix-bound ops zs eq
