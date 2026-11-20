{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.ClosureChain where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter06.Closure using (module Paths)
open import AoP.Chapter08.Paragraph using (Nonempty; _∷⁺_)

-- Exercise 6.34. Write a path with its destination first. Folding a
-- singleton returns its only vertex. Prepending another vertex keeps
-- the result (the starting vertex), provided the new edge exists.
module Chains {A : Set} (R : A ← A) where
  open Paths R using (Star; stop; extend)
  head : Nonempty A → A
  head (x ∷⁺ xs) = x

  data Chain : A ← Nonempty A where
    one : ∀ {a} → Chain a (a ∷⁺ [])
    more : ∀ {a b c cs} → R b c → Chain a (c ∷⁺ cs) → Chain a (b ∷⁺ (c ∷ cs))

  -- The fold carries the previous head together with the starting
  -- vertex. This makes adjacency a local test on the recursive result.
  data Ends : (A × A) ← Nonempty A where
    singleton : ∀ {x} → Ends (x , x) (x ∷⁺ [])
    prepend : ∀ {a b c d ds} → R b c → Ends (c , a) (d ∷⁺ ds) → Ends (b , a) (b ∷⁺ (d ∷ ds))

  endpoints : ∀ {a xs} → Chain a xs → Ends (head xs , a) xs
  endpoints one = singleton
  endpoints (more edge ch) = prepend edge (endpoints ch)

  recover : ∀ {b a xs} → Ends (b , a) xs → (head xs ≡ b) × Chain a xs
  recover singleton = refl , one
  recover (prepend edge e) with recover e
  ... | refl , ch = refl , more edge ch

  unfold-path : ∀ {a b} → Star b a → Σ (Nonempty A) λ xs → (head xs ≡ b) × Chain a xs
  unfold-path stop = (_ ∷⁺ []) , refl , one
  unfold-path (extend edge p) with unfold-path p
  ... | (c ∷⁺ cs) , refl , ch = (_ ∷⁺ (c ∷ cs)) , refl , more edge ch

  fold-path : ∀ {a xs} → Chain a xs → Star (head xs) a
  fold-path one = stop
  fold-path (more edge ch) = extend edge (fold-path ch)

  sound : ∀ {a b} → (Σ (Nonempty A) λ xs → (head xs ≡ b) × Chain a xs) → Star b a
  sound (xs , refl , ch) = fold-path ch
