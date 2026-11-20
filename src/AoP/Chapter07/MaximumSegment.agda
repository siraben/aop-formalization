{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.MaximumSegment where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)

-- Exercise 7.40. Choose a contiguous segment of the input with
-- greatest sum. Empty segments are allowed, with score zero. At a
-- cons, a segment either starts here (a prefix) or lies in the tail.
-- Keep both maxima in a single right fold, without listing segments.
module Solve {A : Set} (zero : A) (_+_ : A → A → A) (_≤_ : A → A → Set)
             (rid : ∀ a → a ≤ a) (tr : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c)
             (cmp : ∀ a b → (a ≤ b) ⊎ (b ≤ a))
             (mono : ∀ x {a b} → a ≤ b → (x + a) ≤ (x + b)) where
  data Prefix : List A → A → Set where
    empty : ∀ {xs} → Prefix xs zero
    extend : ∀ {x xs p} → Prefix xs p → Prefix (x ∷ xs) (x + p)

  data Segment : List A → A → Set where
    start : ∀ {xs p} → Prefix xs p → Segment xs p
    later : ∀ {x xs p} → Segment xs p → Segment (x ∷ xs) p

  record Max (P : A → Set) : Set where
    constructor winner
    field score : A
          attains : P score
          bounds : ∀ {a} → P a → a ≤ score
  open Max

  -- Select the greater of two attainable scores with their joint bound.
  choose : ∀ {P : A → Set} a b → P a → P b → (∀ {c} → P c → (c ≤ a) ⊎ (c ≤ b)) → Max P
  choose a b pa pb cover with cmp a b
  ... | inl ab = winner b pb λ p → merge ab (cover p)
    where merge : ∀ {a b c} → a ≤ b → (c ≤ a) ⊎ (c ≤ b) → c ≤ b
          merge h (inl q) = tr q h
          merge h (inr q) = q
  ... | inr ba = winner a pa λ p → merge ba (cover p)
    where merge : ∀ {a b c} → b ≤ a → (c ≤ a) ⊎ (c ≤ b) → c ≤ a
          merge h (inl q) = q
          merge h (inr q) = tr q h

  prefix-step : ∀ x {xs} → Max (Prefix xs) → Max (Prefix (x ∷ xs))
  prefix-step x p = choose zero (x + score p) empty (extend (attains p)) λ where
    empty → inl (rid zero)
    (extend q) → inr (mono x (bounds p q))

  scan : ∀ xs → Max (Prefix xs) × Max (Segment xs)
  scan [] = winner zero empty (λ { empty → rid zero }) , winner zero (start empty) (λ { (start empty) → rid zero })
  scan (x ∷ xs) with scan xs
  ... | p , s = let q = prefix-step x p in q , choose (score q) (score s) (start (attains q)) (later (attains s)) λ where
    (start r) → inl (bounds q r)
    (later r) → inr (bounds s r)
