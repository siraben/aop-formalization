{-# OPTIONS --safe --without-K #-}
module AoP.UnionImageNaturality where

open import AoP.Prelude
open import AoP.Power using (ℙ; ℰ; _≐_)
open import AoP.Relations using (_←_)
open import AoP.MembershipImageUnion using (image; module Family)

-- §2.3. Apply existential image to the membership square. One route
-- takes the union first, then follows R. The other takes the image of
-- every chosen subset, then collects all members of those images.
module Square {A B : Set} (R : B ← A) (chosen : ℙ A → Set) where
  union-first : B → Set₁
  union-first = image R (Family.union chosen)

  -- A predicate Y belongs to the image family if a chosen X maps to Y.
  -- Comparing subsets by their members permits different presentations.
  images : ℙ B → Set₁
  images = image (λ Y X → ℰ R X ≐ Y) chosen
  images-first : B → Set₁
  images-first = image (λ b Y → Y b) images

  -- Keep the same source element a and supplying subset X on both
  -- routes. The reverse direction uses equality of sets to recover a.
  across : ∀ b → union-first b → images-first b
  across b (a , (r , (X , (x , select)))) =
    ℰ R X , ((a , (r , x)) , (X , (((λ _ p → p) , (λ _ p → p)) , select)))
  back : ∀ b → images-first b → union-first b
  back b (Y , (y , (X , ((into , from) , select)))) with from b y
  ... | a , (r , x) = a , (r , (X , (x , select)))
