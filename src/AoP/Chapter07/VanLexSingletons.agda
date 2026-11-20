{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.VanLexSingletons where

open import AoP.Common.Prelude
open import AoP.Chapter08.Paragraph using (Nonempty; _∷⁺_)
open import AoP.Chapter07.VanLexOrder using (module Order)
open import AoP.Chapter07.VanHeadOrder using (module Law)
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter04.Complement using (⊥)

-- For the printed prefix orientation, splitting every nonempty block
-- into singletons is the unique least partition of a given stream.
module Least (A : Set) where
  open Order A
  open Law A using (keep; empty)
  blocks : List (Nonempty A) → Blocks
  blocks [] = []
  blocks ((a ∷⁺ xs) ∷ ps) = (a ∷ xs) ∷ blocks ps
  stream : List (Nonempty A) → List A
  stream [] = []
  stream ((a ∷⁺ xs) ∷ ps) = a ∷ (xs ++ stream ps)
  singles : List A → Blocks
  singles [] = []
  singles (a ∷ xs) = (a ∷ []) ∷ singles xs

  least : ∀ ps → Q (singles (stream ps)) (blocks ps)
  least [] = tt
  least ((a ∷⁺ []) ∷ ps) = reflP (a ∷ []) , λ _ → least ps
  least ((a ∷⁺ (b ∷ xs)) ∷ ps) = keep a empty , λ r → absurd (tails r)
    where absurd : ∀ {X : Set} → Law.Prefix A (b ∷ xs) [] → X
          absurd ()

  unique : ∀ ps → Q (blocks ps) (singles (stream ps)) → blocks ps ≡ singles (stream ps)
  unique ps p = antisymQ _ _ p (least ps)
