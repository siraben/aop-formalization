{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.LongestPointerDominance where

open import AoP.Common.Prelude
open import AoP.Chapter09.Compression using (module Text)
open import AoP.Chapter09.DictionarySplice using (module Splice)
open import AoP.Chapter09.DecoderPrefix using (module Law)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Common.NatOrder using (_≤_; chain; sum-mono; rid)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Maybe using (just)

-- §9.4: both pointers finish at the same target. The longer copied
-- tail starts from an earlier prefix. Trimming the rival encoding
-- supplies an encoding of that prefix with no greater cost, so its
-- optimal row can replace the rival before paying the pointer charge.
module Law′ {A : Set} (c p : Nat) where
  open Text {A}
  open Splice {A} c p
  open Law {A} c p using (Prefix; simulate)
  dominate : ∀ {x y goal} → Prefix x y → ∀ ps qs i k j n →
    run [] ps ≡ just x → (∀ rs → run [] rs ≡ just x → price ps ≤ price rs) →
    run [] qs ≡ just y → run x (ptr i k ∷ []) ≡ just goal → run y (ptr j n ∷ []) ≡ just goal →
    (run [] (ps ++ (ptr i k ∷ [])) ≡ just goal) × (price (ps ++ (ptr i k ∷ [])) ≤ price (qs ++ (ptr j n ∷ [])))
  dominate path ps qs i k j n ok optimal rival longer shorter with simulate path qs rival
  ... | rs , prefix , le = (resume [] ps (ptr i k ∷ []) ok ∙ longer) , cost
    where
    cost : price (ps ++ (ptr i k ∷ [])) ≤ price (qs ++ (ptr j n ∷ []))
    cost rewrite append-cost ps (ptr i k ∷ []) | append-cost qs (ptr j n ∷ []) =
      sum-mono (chain (optimal rs prefix) le) (rid (p + 0))
