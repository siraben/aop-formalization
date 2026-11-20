{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.DictionarySearch where

open import AoP.Common.Prelude
open import AoP.Chapter09.Compression using (module Text)
open import AoP.Chapter09.CompressionGrowth using (len; module Bound)
open import AoP.Chapter09.CompressionAlphabet using (module Letters)
open import AoP.Chapter09.PointerBounds using (module Bounds)
open import AoP.Chapter09.BoundedWords using (module Words; indices; index-member)
open import AoP.Chapter03.Horner using (map)
open import AoP.Chapter01.Naturality using (_++_; concat)
open import AoP.Chapter05.Subsequences using (_∈_; image; merge)
open import AoP.Appendix.ListProduct using (collect)
open import AoP.Chapter02.Polynomial using (inl; inr)
open import AoP.Common.NatOrder using (rid; chain; _≤_)
open import AoP.Chapter08.ParagraphMinimum using (Dec)
open import AoP.Common.FiniteMinimum using (module Search)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Maybe using (just; nothing)

-- §9.4. Search all encodings of a fixed target using the proven bounds.
-- bytes can account for different symbol and pointer costs. This baseline
-- is exhaustive; it provides an optimality specification for a faster
-- compressor. Duplicate candidate encodings do not affect the minimum.
module Encode {A : Set} (eq? : (x y : A) → Dec (x ≡ y)) (target : List A) where
  open Text {A}
  open Letters {A}
  open Bounds {A}
  open Bound {A}
  n = len target
  ns = indices n
  byOffset = λ i → map (ptr i) ns
  syms = map sym target
  ptrs = concat (map byOffset ns)
  tokens = syms ++ ptrs
  open Words tokens

  over : ∀ {ops} → Uses target ops → Bounded n ops → Over ops
  over end end = empty
  over (literal m tail) (literal b) = extend (merge syms ptrs (inl (image sym m))) (over tail b)
  over (pointer {i} {k} tail) (pointer small short b) = extend
    (merge syms ptrs (inr (collect byOffset (index-member i n small) (image (ptr i) (index-member k n short))))) (over tail b)

  size′ : ∀ k → k ≡ grow k 0
  size′ zero = refl
  size′ (suc k) = cong suc (size′ k) ∙ back (grow-suc k 0)
    where back : ∀ {a b : Nat} → a ≡ b → b ≡ a
          back refl = refl

  Valid : List Code → Set
  Valid ops = run [] ops ≡ just target
  eligible : ∀ ops → Valid ops → ops ∈ words n
  eligible ops eq = complete n fits (over (alphabet ops [] eq) (all-bounded ops [] eq))
    where
    fits : len ops ≤ n
    fits rewrite size′ (len ops) = bound ops [] eq

  list? : (xs ys : List A) → Dec (xs ≡ ys)
  list? [] [] = inl refl
  list? [] (_ ∷ _) = inr (λ ())
  list? (_ ∷ _) [] = inr (λ ())
  list? (x ∷ xs) (y ∷ ys) with eq? x y | list? xs ys
  ... | inl refl | inl refl = inl refl
  ... | inr no | _ = inr λ { refl → no refl }
  ... | _ | inr no = inr λ { refl → no refl }

  valid? : ∀ ops → Dec (Valid ops)
  valid? ops with run [] ops
  ... | nothing = inr (λ ())
  ... | just xs with list? xs target
  ...   | inl refl = inl refl
  ...   | inr no = inr λ { refl → no refl }

  module Minimum (bytes : List Code → Nat) where
    open Search Valid valid? bytes
    Result′ = Σ (List Code) λ ops → Valid ops × (∀ ys → Valid ys → bytes ops ≤ bytes ys)
    encode : Result′
    encode with scan (words n)
    ... | best ops _ eq least = ops , eq , λ ys valid → least ys (eligible ys valid) valid
    ... | none no with no (literals target) (eligible (literals target) (round-trip target)) (round-trip target)
    ...   | ()
