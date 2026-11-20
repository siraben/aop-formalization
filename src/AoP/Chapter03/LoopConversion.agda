{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.LoopConversion where

open import AoP.Common.Prelude
open import AoP.Chapter02.Folds using (⦅_∣_⦆)
open import AoP.Chapter01.Snoc using (Snoc; ε; _▻_; append; toSnoc; foldl)
open import AoP.Chapter03.SnocLoop using (module Loop)
open import AoP.Chapter01.ConversionFold using (convert; spec; catconv)
open import AoP.Chapter01.Naturality using (_++_)
private variable A B : Set

-- Exercise 3.51. Consume either representation directly. The snoc loop
-- visits the last element first, so cons builds the original order at
-- the front of the suffix. More generally the suffix can already be
-- reduced to a single value; replace cons by the reducing operation.
convert-loop : (xs : Snoc A) (ys : List A) → convert xs ++ ys ≡ Loop.loop (λ p → fst p ∷ snd p) (xs , ys)
convert-loop xs ys = spec xs ys ∙ same xs ys
  where
  same : ∀ xs ys → catconv xs ys ≡ Loop.loop (λ p → fst p ∷ snd p) (xs , ys)
  same ε ys = refl
  same (xs ▻ a) ys = same xs (a ∷ ys)

module Reduce (f : A → B → B) where
  run = Loop.loop (λ p → f (fst p) (snd p))
  append-law : ∀ e xs ys → ⦅ e ∣ f ⦆ (xs ++ ys) ≡ ⦅ ⦅ e ∣ f ⦆ ys ∣ f ⦆ xs
  append-law e [] ys = refl
  append-law e (a ∷ xs) ys = cong (f a) (append-law e xs ys)

  simulate : ∀ xs b → ⦅ b ∣ f ⦆ (convert xs) ≡ run (xs , b)
  simulate ε b = refl
  simulate (xs ▻ a) b = append-law b (convert xs) (a ∷ []) ∙ simulate xs (f a b)

-- In the other direction update the state as each cons head arrives.
module Forward (e : B) (f : B → A → B) where
  loop : List A → B → B
  loop [] b = b
  loop (a ∷ as) b = loop as (f b a)

  invariant : ∀ xs ys → foldl e f (append xs ys) ≡ loop ys (foldl e f xs)
  invariant xs [] = refl
  invariant xs (a ∷ as) = invariant (xs ▻ a) as

  correct : ∀ ys → foldl e f (toSnoc ys) ≡ loop ys e
  correct = invariant ε
