{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.SegmentFusion where

open import AoP.Common.Prelude
open import AoP.Chapter07.MaximumSegment using (module Solve)
open import AoP.Chapter02.Polynomial using (_⊎_)

-- Exercise 7.40. Before maximizing anything, fuse scoring with the
-- relational prefix fold. The stopping branch scores zero; retaining
-- a head adds it to the score produced by the recursive branch.
module Law {A : Set} (zero : A) (_+_ : A → A → A) (_≤_ : A → A → Set)
           (rid : ∀ a → a ≤ a) (tr : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c)
           (cmp : ∀ a b → (a ≤ b) ⊎ (b ≤ a))
           (mono : ∀ x {a b} → a ≤ b → (x + a) ≤ (x + b)) where
  open Solve zero _+_ _≤_ rid tr cmp mono
  data Pre : List A → List A → Set where
    nil : ∀ {xs} → Pre [] xs
    cons : ∀ {x ys xs} → Pre ys xs → Pre (x ∷ ys) (x ∷ xs)
  sum : List A → A
  sum [] = zero
  sum (x ∷ xs) = x + sum xs

  fuse : ∀ {ys xs} → Pre ys xs → Prefix xs (sum ys)
  fuse nil = empty
  fuse (cons p) = extend (fuse p)

  recover : ∀ {xs p} → Prefix xs p → Σ (List A) λ ys → Pre ys xs × (sum ys ≡ p)
  recover empty = [] , nil , refl
  recover (extend {x} p) with recover p
  ... | ys , sub , refl = (x ∷ ys) , cons sub , refl

  data Suffix : List A → List A → Set where
    here : ∀ {xs} → Suffix xs xs
    skip : ∀ {x ys xs} → Suffix ys xs → Suffix ys (x ∷ xs)

  decompose : ∀ {xs p} → Segment xs p → Σ (List A) λ zs → Suffix zs xs × Prefix zs p
  decompose (start pre) = _ , here , pre
  decompose (later s) with decompose s
  ... | zs , suf , pre = zs , skip suf , pre

  assemble : ∀ {xs zs p} → Suffix zs xs → Prefix zs p → Segment xs p
  assemble here pre = start pre
  assemble (skip suf) pre = later (assemble suf pre)

  -- Maximize the prefix at *each* suffix, then maximize these scores.
  -- The segment winner belongs to some suffix. In a preorder that
  -- suffix's prefix winner can be tied without being equal, so compare
  -- the two maxima in both directions rather than identifying scores.
  BestAtSuffix : List A → A → Set
  BestAtSuffix xs v = Σ (List A) λ zs → Suffix zs xs × (Max.score (fst (scan zs)) ≡ v)

  suffix-upper : ∀ xs {v} → BestAtSuffix xs v → v ≤ Max.score (snd (scan xs))
  suffix-upper xs (zs , suf , refl) = Max.bounds (snd (scan xs)) (assemble suf (Max.attains (fst (scan zs))))

  winning-suffix : ∀ xs → Σ A λ v → BestAtSuffix xs v × (Max.score (snd (scan xs)) ≤ v)
  winning-suffix xs with decompose (Max.attains (snd (scan xs)))
  ... | zs , suf , pre = _ , (zs , suf , refl) , Max.bounds (fst (scan zs)) pre

  suffix-maximum : ∀ xs → Max (BestAtSuffix xs)
  suffix-maximum xs with winning-suffix xs
  ... | v , witness , upper = winner v witness (λ p → tr (suffix-upper xs p) upper)
