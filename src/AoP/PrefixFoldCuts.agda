{-# OPTIONS --safe --without-K #-}
module AoP.PrefixFoldCuts where

open import AoP.Prelude
open import AoP.Naturality using (_++_)
open import AoP.Relations using (Fold; nil; cons)
open import AoP.Closure using (module Paths)

-- §5.6. A cut of xs keeps its left part. The relational cons fold
-- either stops immediately or retains the head of the recursive cut.
module Law {A : Set} where
  data Step : List A → A × List A → Set where
    halt : ∀ {a p} → Step [] (a , p)
    retain : ∀ {a p} → Step (a ∷ p) (a , p)
  Prefix = Fold (_≡ []) Step
  Cut : List A → List A → Set
  Cut p xs = Σ _ λ tail → p ++ tail ≡ xs
  to-cut : ∀ {xs p} → Prefix p xs → Cut p xs
  to-cut (nil refl) = [] , refl
  to-cut (cons halt tail) = _ , refl
  to-cut (cons {x} retain tail) with to-cut tail
  ... | suffix , eq = suffix , cong (x ∷_) eq
  empty : ∀ xs → Prefix [] xs
  empty [] = nil refl
  empty (a ∷ xs) = cons halt (empty xs)
  build : ∀ p tail → Prefix p (p ++ tail)
  build [] tail = empty tail
  build (a ∷ p) tail = cons retain (build p tail)
  from-cut : ∀ {xs p} → Cut p xs → Prefix p xs
  from-cut {p = p} (suffix , refl) = build p suffix

  -- A second presentation discards one last element at each step.
  data Drop : List A → List A → Set where
    last : ∀ p a → Drop p (p ++ (a ∷ []))
  module P = Paths Drop
  prepend : ∀ a {p xs} → P.Star p xs → P.Star (a ∷ p) (a ∷ xs)
  prepend a P.stop = P.stop
  prepend a (P.extend (last p x) h) = P.extend (last (a ∷ p) x) (prepend a h)
  clear : ∀ xs → P.Star [] xs
  clear [] = P.stop
  clear (a ∷ xs) = P.extend (last [] a) (prepend a (clear xs))
  remove : ∀ p tail → P.Star p (p ++ tail)
  remove [] tail = clear tail
  remove (a ∷ p) tail = prepend a (remove p tail)
  regroup : ∀ p (a : A) tail → (p ++ (a ∷ [])) ++ tail ≡ p ++ (a ∷ tail)
  regroup [] a tail = refl
  regroup (x ∷ p) a tail = cong (x ∷_) (regroup p a tail)
  recover : ∀ {p xs} → P.Star p xs → Cut p xs
  recover {p} P.stop = [] , unit p
    where unit : ∀ (q : List A) → q ++ [] ≡ q
          unit [] = refl
          unit (a ∷ q) = cong (a ∷_) (unit q)
  recover (P.extend (last p a) h) with recover h
  ... | tail , eq rewrite regroup p a tail = (a ∷ tail) , eq
