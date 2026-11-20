{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.ProductSymmetry where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.FunctorIso using (module Arrows)

-- Exercise 2.26. In an arbitrary category a product arrow is determined
-- by two observations. Swapping exchanges those observations; swapping
-- twice restores both, hence restores the original arrow.
module Products {o h e} (C : Category o h e) where
  open Category C
  module Chosen (_⊗_ : Obj → Obj → Obj)
    (l : ∀ {A B} → Hom (A ⊗ B) A) (r : ∀ {A B} → Hom (A ⊗ B) B)
    (pair : ∀ {X A B} → Hom X A → Hom X B → Hom X (A ⊗ B))
    (fst-law : ∀ {X A B} (a : Hom X A) (b : Hom X B) → l ∘ pair a b ≈ a)
    (snd-law : ∀ {X A B} (a : Hom X A) (b : Hom X B) → r ∘ pair a b ≈ b)
    (ext : ∀ {X A B} (f g : Hom X (A ⊗ B)) → l ∘ f ≈ l ∘ g → r ∘ f ≈ r ∘ g → f ≈ g) where

    swap : ∀ {A B} → Hom (A ⊗ B) (B ⊗ A)
    swap = pair r l

    -- Observe a composite by first reducing its outer arrow.
    observe : ∀ {X Y Z W} (p : Hom Z W) (f : Hom Y Z) (g : Hom X Y) {q} →
              p ∘ f ≈ q → p ∘ (f ∘ g) ≈ q ∘ g
    observe p f g law = transitive (symmetric (assoc p f g)) (compose-cong law reflexive)

    twice : ∀ {A B} → swap {B} {A} ∘ swap ≈ identity
    twice = ext _ _ (transitive (observe l swap swap (fst-law _ _))
                                (transitive (snd-law _ _) (symmetric (unitʳ l))))
                    (transitive (observe r swap swap (snd-law _ _))
                                (transitive (fst-law _ _) (symmetric (unitʳ r))))

    iso : ∀ A B → Arrows.Inverse C (swap {A} {B})
    iso A B = Arrows.inverse swap twice twice

    cross : ∀ {A B X Y} → Hom A X → Hom B Y → Hom (A ⊗ B) (X ⊗ Y)
    cross f g = pair (f ∘ l) (g ∘ r)

    natural : ∀ {A B X Y} (f : Hom A X) (g : Hom B Y) → swap ∘ cross f g ≈ cross g f ∘ swap
    natural f g = ext _ _ first second
      where
      first : l ∘ (swap ∘ cross f g) ≈ l ∘ (cross g f ∘ swap)
      first = transitive (observe l swap _ (fst-law _ _)) (transitive (snd-law _ _)
        (symmetric (transitive (observe l _ swap (fst-law _ _))
          (transitive (assoc g l swap) (compose-cong reflexive (fst-law _ _))))))
      second : r ∘ (swap ∘ cross f g) ≈ r ∘ (cross g f ∘ swap)
      second = transitive (observe r swap _ (snd-law _ _)) (transitive (fst-law _ _)
        (symmetric (transitive (observe r _ swap (snd-law _ _))
          (transitive (assoc f r swap) (compose-cong reflexive (snd-law _ _))))))
