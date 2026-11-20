{-# OPTIONS --safe --without-K #-}
module AoP.Chapter10.BagAlgebraFibre where

open import AoP.Common.Prelude
open import AoP.Chapter01.Snoc using (Snoc; ε; _▻_; foldl)

-- Exercise 10.8. Read the equation on inverse fibres. On a bag
-- extended by j, first choose a listing of the smaller bag, then
-- insert j. Surjectivity lets the permutation fold do the splitting.
module Law {A Bag : Set} (zero : Bag) (put : Bag → A → Bag)
           (Add : Snoc A → A → Snoc A → Set) where
  bagify = foldl zero put
  Same : Snoc A → Snoc A → Set
  Same xs ys = bagify xs ≡ bagify ys
  data Fold : Snoc A → Snoc A → Set where
    nil : Fold ε ε
    step : ∀ {xs ys zs j} → Fold xs ys → Add ys j zs → Fold (xs ▻ j) zs

  module Derive (represent : ∀ b → Σ (Snoc A) λ xs → bagify xs ≡ b)
                (into : ∀ {xs ys} → Same xs ys → Fold xs ys)
                (out : ∀ {xs ys} → Fold xs ys → Same xs ys) where
    empty-out : ∀ ys → zero ≡ bagify ys → ε ≡ ys
    empty-out ys eq with into {ε} {ys} eq
    ... | nil = refl
    empty-in : ∀ ys → ε ≡ ys → zero ≡ bagify ys
    empty-in .ε refl = refl

    split : ∀ b j zs → put b j ≡ bagify zs → Σ (Snoc A) λ ys → (b ≡ bagify ys) × Add ys j zs
    split b j zs eq with represent b
    ... | xs , refl with into {xs ▻ j} {zs} eq
    ...   | step p i = _ , out p , i
    join : ∀ b j zs → (Σ (Snoc A) λ ys → (b ≡ bagify ys) × Add ys j zs) → put b j ≡ bagify zs
    join .(bagify ys) j zs (ys , refl , i) = out (step (into {ys} {ys} refl) i)
