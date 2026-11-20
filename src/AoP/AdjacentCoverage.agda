{-# OPTIONS --safe --without-K #-}
module AoP.AdjacentCoverage where

open import AoP.Prelude
open import AoP.Bump using (module Prune)
open import AoP.AdjacentThin using (module Algorithm)
open import AoP.Subsequences using (_∈_; here; there)
open import AoP.Thinning using (Thin; thin; thin-compose; thin-id)

-- Exercise 8.13. Replacing two comparable heads by their winner is
-- itself a thinning. Compose that local proof with the recursive one.
-- For incomparable heads, keep the first and lift the recursive proof.
module Law {A : Set} (Q : A → A → Set) (rr : ∀ x → Q x x)
           (tr : ∀ {x y z} → Q x y → Q y z → Q x z) where
  module P = Prune Q rr tr
  module Run (cmp : ∀ x y → P.Comparison x y) where
    module C = P.Algorithm cmp
    module D = Algorithm.Run Q rr tr cmp
    pending : ∀ a xs → C.Covers (D.pending a xs) (a ∷ xs)
    pending a [] = thin-id rr
    pending a (b ∷ xs) with cmp a b | C.local a (b ∷ xs)
    ... | P.first ab | local = thin-compose tr (pending a xs) local
    ... | P.second ba | local = thin-compose tr (pending b xs) local
    ... | P.retain | _ = C.lift a (pending b xs)

    correct : ∀ xs → C.Covers (D.thinlist xs) xs
    correct [] = thin-id rr
    correct (a ∷ xs) = pending a xs
