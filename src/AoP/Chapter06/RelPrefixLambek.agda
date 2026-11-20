{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.RelPrefixLambek where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _⊆_)
open import AoP.Chapter06.PrefixLambek using (module Law)
open import AoP.Chapter06.FixedPoint using (module KnasterTarski)

-- Exercise 6.5, specialized to the book's hom-order. Use mutual
-- inclusion for equality of relations. The reverse edge is the fold
-- into the lifted algebra in exactly the category of this hom-order.
module At {A B : Set} (Φ : (B ← A) → B ← A)
          (mono : ∀ {R S} → R ⊆ S → Φ R ⊆ Φ S) where
  private
    compose : ∀ {R S T : B ← A} → R ⊆ S → S ⊆ T → R ⊆ T
    compose p q x = q (p x)
    Incl : (B ← A) → (B ← A) → Set
    Incl R S = R ⊆ S
  module K = KnasterTarski Incl (λ {x} {y} {z} → compose {x} {y} {z}) Φ (λ {x} {y} → mono {x} {y})
  module L = Law Incl (λ _ x → x) (λ {x} {y} {z} → compose {x} {y} {z}) Φ (λ {x} {y} → mono {x} {y})
  module From {μ : B ← A} (inf : K.Infimum μ) where
    module P = K.Proof inf
    module I = L.Least P.fold (λ {x} → P.least x)
    fixed : (Φ μ ⊆ μ) × (μ ⊆ Φ μ)
    fixed = P.fold , I.out
