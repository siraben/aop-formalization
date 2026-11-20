{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.VanSplitCost where

open import AoP.Common.Prelude
open import AoP.Chapter08.Paragraph using (Nonempty; _∷⁺_)
open import AoP.Common.NatOrder using (_≤_; rid; chain)
open import Agda.Builtin.Nat using (Nat)

-- Exercise 7.57. A nonadditive objective can depend on the whole
-- partition. It suffices that peeling off the first item of a block
-- never increases cost, even with a prefix of finished singleton
-- blocks and an arbitrary suffix of blocks. No additivity is used.
module Law {A : Set} (cost : List (Nonempty A) → Nat) where
  single : A → Nonempty A
  single a = a ∷⁺ []
  front : List A → List (Nonempty A) → List (Nonempty A)
  front [] ps = ps
  front (a ∷ as) ps = single a ∷ front as ps

  Peel = ∀ pre a b bs rest → cost (front pre (single a ∷ (b ∷⁺ bs) ∷ rest)) ≤
                              cost (front pre ((a ∷⁺ (b ∷ bs)) ∷ rest))
  -- Carry finished singleton blocks through the induction.
  module Steps (peel : Peel) where
    snoc : List A → A → List A
    snoc [] a = a ∷ []
    snoc (x ∷ xs) a = x ∷ snoc xs a
    shift : ∀ pre a rest → front (snoc pre a) rest ≡ front pre (single a ∷ rest)
    shift [] a rest = refl
    shift (x ∷ xs) a rest = cong (single x ∷_) (shift xs a rest)
    block : ∀ pre a as rest → cost (front pre (front (a ∷ as) rest)) ≤ cost (front pre ((a ∷⁺ as) ∷ rest))
    block pre a [] rest = rid _
    block pre a (b ∷ bs) rest with block (snoc pre a) b bs rest
    ... | le rewrite shift pre a (front (b ∷ bs) rest) | shift pre a ((b ∷⁺ bs) ∷ rest) = chain le (peel pre a b bs rest)

    open import AoP.Chapter01.Naturality using (_++_)
    append : ∀ pre xs rest → front (pre ++ xs) rest ≡ front pre (front xs rest)
    append [] xs rest = refl
    append (a ∷ pre) xs rest = cong (single a ∷_) (append pre xs rest)
    split-all : List (Nonempty A) → List (Nonempty A)
    split-all [] = []
    split-all ((a ∷⁺ as) ∷ ps) = front (a ∷ as) (split-all ps)
    all : ∀ pre ps → cost (front pre (split-all ps)) ≤ cost (front pre ps)
    all pre [] = rid _
    all pre ((a ∷⁺ as) ∷ ps) with all (pre ++ (a ∷ as)) ps
    ... | le rewrite append pre (a ∷ as) (split-all ps) | append pre (a ∷ as) ps = chain le (block pre a as ps)
