{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.AppendEquation where

open import AoP.Common.Prelude
open import AoP.Chapter01.Naturality using (_++_)
open import AoP.Chapter02.Folds using (unique)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter02.Products using ([_,_])
open import AoP.Chapter03.DistributedCase using (cross)

-- Exercise 3.31 in Fun. Carry the right list past the constructor tag.
-- For nil it is the result; for cons it belongs to the recursive call
-- on the tail. This combines both defining equations into (3.6).
module Calculate {A : Set} (cat : List A × List A → List A) where
  Layer = ⊤ ⊎ (A × List A)
  build : Layer → List A
  build = [ (λ _ → []) , (λ p → fst p ∷ snd p) ]

  φ : Layer × List A → (⊤ × List A) ⊎ (A × (List A × List A))
  φ (inl u , ys) = inl (u , ys)
  φ (inr (a , xs) , ys) = inr (a , xs , ys)

  rhs : Layer × List A → List A
  rhs p = [ snd , (λ q → fst q ∷ cat (snd q)) ] (φ p)

  Combined = ∀ p → cat (cross build (λ y → y) p) ≡ rhs p
  Branches = (∀ ys → cat ([] , ys) ≡ ys) ×
             (∀ a xs ys → cat (a ∷ xs , ys) ≡ a ∷ cat (xs , ys))

  separate : Combined → Branches
  separate law = (λ ys → law (inl tt , ys)) , (λ a xs ys → law (inr (a , xs) , ys))

  combine : Branches → Combined
  combine (base , step) (inl tt , ys) = base ys
  combine (base , step) (inr (a , xs) , ys) = step a xs ys

  -- Fixing the right list turns the two branches into an ordinary fold
  -- on the left list. Its empty case returns the saved right list and
  -- its step restores a single head. Thus (3.6) determines cat even
  -- though both operands appear in the original equation.
  determined : Combined → ∀ xs ys → cat (xs , ys) ≡ xs ++ ys
  determined law xs ys = unique (λ zs → cat (zs , ys)) ys _∷_
    (fst (separate law) ys) (λ a zs → snd (separate law) a zs ys) xs

module Append {A : Set} where
  module C = Calculate {A} (λ p → fst p ++ snd p)
  solves : C.Combined
  solves = C.combine ((λ ys → refl) , (λ a xs ys → refl))
