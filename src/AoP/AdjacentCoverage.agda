{-# OPTIONS --safe --without-K #-}
module AoP.AdjacentCoverage where

open import AoP.Prelude
open import AoP.Bump using (module Prune)
open import AoP.AdjacentThin using (module Algorithm)
open import AoP.Subsequences using (Subseq)
open import AoP.Relations using (cons; nil)
open import AoP.Refinement using (skip; keep)
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

    -- Reinsert an eliminated second input cell into the subsequence
    -- witness. The first cell may itself have been discarded later.
    insert-second : ∀ {ys : List A} {a xs} b → Subseq ys (a ∷ xs) → Subseq ys (a ∷ b ∷ xs)
    insert-second b (cons skip p) = cons skip (cons skip p)
    insert-second b (cons keep p) = cons keep (cons skip p)

    pending-order : ∀ a xs → Subseq (D.pending a xs) (a ∷ xs)
    pending-order a [] = cons keep (nil refl)
    pending-order a (b ∷ xs) with cmp a b
    ... | P.first _ = insert-second b (pending-order a xs)
    ... | P.second _ = cons skip (pending-order b xs)
    ... | P.retain = cons keep (pending-order b xs)

    ordered : ∀ xs → Subseq (D.thinlist xs) xs
    ordered [] = nil refl
    ordered (a ∷ xs) = pending-order a xs
