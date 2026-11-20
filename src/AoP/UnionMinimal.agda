{-# OPTIONS --safe --without-K #-}
module AoP.UnionMinimal where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Thinning using (Min)
open import AoP.MinimalComparison using (Test)
open import AoP.WellSupported using (Supported; module Cover)

-- Exercise 7.32. Keep all locally minimal elements, including tied
-- or incomparable ones. To test a challenger b omitted by this filter,
-- use 7.31 to find a retained challenger c below b in the same set.
module Law {I A : Set} (R : A ← A) (rr : ∀ a → R a a)
           (tr : ∀ {a b c} → R a b → R b c → R a c)
           (support : Supported R) (family : I → A → Set) where
  Whole Kept : A → Set
  Whole a = Σ I λ i → family i a
  Kept a = Σ I λ i → Min (Test R) a (family i)

  reduce : ∀ {a} → Min (Test R) a Whole → Min (Test R) a Kept
  reduce ((i , xa) , minimal) = (i , xa , (λ b xb → minimal b (i , xb))) ,
    λ { b (j , xb , _) → minimal b (j , xb) }

  restore : ∀ {a} → Min (Test R) a Kept → Min (Test R) a Whole
  restore {a} ((i , xa , _) , minimal) = (i , xa) , reverse
    where
    reverse : ∀ b → Whole b → R b a → R a b
    reverse b (j , xb) ba with Cover.below R rr tr support (family j) b xb
    ... | c , cb , kept = tr (minimal c (j , kept) (tr cb ba)) cb
