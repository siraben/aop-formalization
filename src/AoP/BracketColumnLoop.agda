{-# OPTIONS --safe --without-K #-}
module AoP.BracketColumnLoop where

open import AoP.Prelude
open import AoP.Snoc using (Snoc; ε; _▻_; foldl)
open import AoP.PrefixLoop using (module Law)

-- §9.3, (9.9). Represent a nonempty interval by its head and snoc
-- tail. Its singleton column starts at the tip; each new endpoint
-- contributes one row. The mixing operation is a parameter here.
module Column {A T Row : Set} (tip : A → T) (row : Snoc A → Row)
              (mix : Snoc T → Row → T) where
  start : A → Snoc T
  start a = ε ▻ tip a
  next : Snoc T → Row → Snoc T
  next ts r = ts ▻ mix ts r

  open Law start row next
  array : Snoc A → Snoc Row
  array xs = mapped (prefixes xs)
  process : A → Snoc Row → Snoc T
  process a = foldl (start a) next

  col : A → Snoc A → Snoc T
  col a ε = start a
  col a (xs ▻ x) = next (col a xs) (row (xs ▻ x))

  -- Apply the sufficient direction of the prefix-loop law to (9.8).
  equation : ∀ a xs → col a xs ≡ process a (array xs)
  equation = Characterise.sufficient col (λ a → refl) (λ a xs x → refl)
