{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.FiniteImageFactor where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter05.Subsequences using (_∈_; here; there)
open import AoP.Chapter04.DecidableImageFactor using (module Factor)

-- Given an exhaustive list of inputs, decide each output fibre by a
-- left-to-right scan. Duplicate inputs or duplicate outputs cause no
-- ambiguity in the intermediate image type: only the output is stored.
module Table {A B : Set} (f : A → B) (rows : List A)
  (all : ∀ a → a ∈ rows) (eq? : ∀ b c → (b ≡ c) ⊎ (b ≡ c → ⊥)) where
  open Factor f
  scan : ∀ b xs → Fibre b ⊎ (∀ a → a ∈ xs → f a ≡ b → ⊥)
  scan b [] = inr (λ a ())
  scan b (x ∷ xs) with eq? (f x) b
  ... | inl hit = inl (x , hit)
  ... | inr miss with scan b xs
  ...   | inl w = inl w
  ...   | inr absent = inr λ where
    _ here hit → miss hit
    a (there at) hit → absent a at hit
  test : ∀ b → Fibre b ⊎ (Fibre b → ⊥)
  test b with scan b rows
  ... | inl w = inl w
  ... | inr no = inr λ { (a , hit) → no a (all a) hit }
  module Image = Build test
