{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.ContainerEmpty where

open import AoP.Common.Prelude
open import AoP.Chapter04.Complement using (⊥)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)

-- Exercise 6.21 for containers: a value has a shape and a label at
-- each position of that shape. Entire membership chooses a label in
-- every value. An empty-labelled value could only have zero positions.
module Law (Shape : Set) (Pos : Shape → Set) where
  F : Set → Set
  F A = Σ Shape λ s → Pos s → A

  Member : ∀ {A} → A → F A → Set
  Member a (s , labels) = Σ (Pos s) λ i → labels i ≡ a

  Entire : Set₁
  Entire = ∀ {A} (v : F A) → Σ A λ a → Member a v

  forward : Entire → F ⊥ → ⊥
  forward entire v = fst (entire v)

  -- Constructively, emptiness of F ⊥ excludes positionless shapes.
  -- Deciding whether each shape has a position turns this into a
  -- choice of position, as required by the Boolean statement.
  backward : ((s : Shape) → Pos s ⊎ (Pos s → ⊥)) → (F ⊥ → ⊥) → Entire
  backward decide empty (s , labels) with decide s
  ... | inl i = labels i , i , refl
  ... | inr none with empty (s , none)
  ...   | ()
