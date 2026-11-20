{-# OPTIONS --safe --without-K #-}
module AoP.AppendEquation where

open import AoP.Prelude
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Products using ([_,_])
open import AoP.DistributedCase using (cross)

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
