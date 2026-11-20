{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.Entab where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import AoP.Common.Prelude
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter10.Detab
open import AoP.Chapter10.TabFree
open import AoP.Chapter10.TabStop
open import AoP.Chapter01.Snoc using (ε; _▻_)

-- §10.2. Buffer a run of spaces until it reaches the next stop. Then a
-- single tab replaces the run. At a letter, newline or EOF, flush any
-- short remainder literally. For width four, `A   B  ` becomes
-- `A<TAB>B  `: the final two spaces must not be lost.
module Encode {A : Set} (n : Nat) where
  open Expand {A} n
  open Image {A} n
  open Rewrite {A} n

  data Test (k m : Nat) : Set where
    same : k ≡ m → Test k m
    different : (k ≡ m → ⊥) → Test k m

  test : ∀ k m → Test k m
  test zero zero = same refl
  test zero (suc _) = different (λ ())
  test (suc _) zero = different (λ ())
  test (suc k) (suc m) with test k m
  ... | same refl = same refl
  ... | different neq = different (λ eq → neq (cong pred eq))
    where
    pred : Nat → Nat
    pred zero = zero
    pred (suc i) = i

  record Buffer (target : Text) : Set where
    constructor buf
    field
      code : Text
      pending : Nat
      represents : blanks (detab code) pending ≡ target

  snoc-blanks : ∀ xs k → blanks xs (suc k) ≡ blanks xs k ▻ blank
  snoc-blanks xs zero = refl
  snoc-blanks xs (suc k) = snoc-blanks (xs ▻ blank) k

  add-space : ∀ {s} → Buffer s → Buffer (s ▻ blank)
  add-space (buf xs k inv) with test k (position (detab xs))
  ... | same refl = buf (xs ▻ tab) 0 (snoc-blanks (detab xs) (position (detab xs)) ∙ cong (_▻ blank) inv)
  ... | different _ = buf xs (suc k) (snoc-blanks (detab xs) k ∙ cong (_▻ blank) inv)

  flush : ∀ {s} → Buffer s → Σ Text (λ xs → detab xs ≡ s)
  flush (buf xs k inv) = blanks xs k , (literal-blanks k xs ∙ inv)

  encode : ∀ {s} → Plain s → Buffer s
  encode empty = buf ε 0 refl
  encode (space p) = add-space (encode p)
  encode (line p) with flush (encode p)
  ... | xs , eq = buf (xs ▻ newline) 0 (cong (_▻ newline) eq)
  encode (char a p) with flush (encode p)
  ... | xs , eq = buf (xs ▻ glyph a) 0 (cong (_▻ glyph a) eq)

  entab : ∀ {s} → Plain s → Σ Text (λ xs → detab xs ≡ s)
  entab p = flush (encode p)
