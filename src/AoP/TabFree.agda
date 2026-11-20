{-# OPTIONS --safe --without-K #-}
module AoP.TabFree where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import AoP.Prelude
open import AoP.Detab
open import AoP.Snoc using (ε; _▻_)

-- §10.2. Entabbing can only be a right inverse on *expanded* texts:
-- no input to detab can produce a literal tab. The image is exactly
-- the tab-free texts, because those texts are fixed by expansion. This
-- identifies the feasible domain before asking for a shortest encoding.
module Image {A : Set} (n : Nat) where
  open Expand {A} n
  data Plain : Text → Set where
    empty : Plain ε
    space : ∀ {s} → Plain s → Plain (s ▻ blank)
    line : ∀ {s} → Plain s → Plain (s ▻ newline)
    char : ∀ {s} a → Plain s → Plain (s ▻ glyph a)

  spaces : ∀ k {s} → Plain s → Plain (blanks s k)
  spaces zero p = p
  spaces (suc k) p = spaces k (space p)

  plain : ∀ s → Plain (detab s)
  plain ε = empty
  plain (s ▻ tab) = spaces (suc (position (detab s))) (plain s)
  plain (s ▻ blank) = space (plain s)
  plain (s ▻ newline) = line (plain s)
  plain (s ▻ glyph a) = char a (plain s)

  fixed : ∀ {s} → Plain s → detab s ≡ s
  fixed empty = refl
  fixed (space p) = cong (_▻ blank) (fixed p)
  fixed (line p) = cong (_▻ newline) (fixed p)
  fixed (char a p) = cong (_▻ glyph a) (fixed p)

  idempotent : ∀ s → detab (detab s) ≡ detab s
  idempotent s = fixed (plain s)
