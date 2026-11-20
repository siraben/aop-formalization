{-# OPTIONS --safe --without-K #-}
module AoP.TabStop where

open import Agda.Builtin.Nat using (Nat; suc)
open import AoP.Prelude
open import AoP.Snoc using (ε; _▻_; foldl; _++_)
open import AoP.Detab

-- §10.2. A tab can replace the entire run of blanks leading to the
-- next stop, even when text follows it. The important state is the
-- *expanded* prefix: a preceding tab makes raw character count wrong.
-- For example, after A at width four the replacement consumes three
-- blanks; after a whole tab it consumes four, not three.
module Rewrite {A : Set} (n : Nat) where
  open Expand {A} n

  -- Expansion is a left fold: once prefixes have the same expansion,
  -- no common continuation can distinguish them.
  context : ∀ {xs ys} → detab xs ≡ detab ys → ∀ rest → detab (xs ++ rest) ≡ detab (ys ++ rest)
  context eq ε = eq
  context eq (rest ▻ c) = cong (λ s → expand s c) (context eq rest)

  literal-blanks : ∀ k xs → detab (blanks xs k) ≡ blanks (detab xs) k
  literal-blanks 0 xs = refl
  literal-blanks (suc k) xs = literal-blanks k (xs ▻ blank)

  replace : ∀ xs rest → let k = suc (position (detab xs)) in
            detab (blanks xs k ++ rest) ≡ detab ((xs ▻ tab) ++ rest)
  replace xs rest = context {xs = blanks xs k} {ys = xs ▻ tab} prefix rest
    where
    k = suc (position (detab xs))
    prefix : detab (blanks xs k) ≡ detab (xs ▻ tab)
    prefix = begin
      detab (blanks xs k)   ≡⟨ literal-blanks k xs ⟩
      blanks (detab xs) k   ≡⟨⟩
      detab (xs ▻ tab) ∎
