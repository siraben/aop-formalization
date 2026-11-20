{-# OPTIONS --safe --without-K #-}
module AoP.ProductAssociator where

open import AoP.Categories
open import AoP.FunctorIso using (module Arrows)

-- Exercise 2.26. Encode three arrows from a common source in either
-- bracketing. Reassociation preserves the three observations. Applying
-- it to a packed triple is enough to compute both inverse composites.
module Triple {o h e} (C : Category o h e) where
  open Category C
  module Products (_⊗_ : Obj → Obj → Obj)
    (l : ∀ {A B} → Hom (A ⊗ B) A) (r : ∀ {A B} → Hom (A ⊗ B) B)
    (pair : ∀ {X A B} → Hom X A → Hom X B → Hom X (A ⊗ B))
    (fst-law : ∀ {X A B} (a : Hom X A) (b : Hom X B) → l ∘ pair a b ≈ a)
    (snd-law : ∀ {X A B} (a : Hom X A) (b : Hom X B) → r ∘ pair a b ≈ b)
    (ext : ∀ {X A B} (f g : Hom X (A ⊗ B)) → l ∘ f ≈ l ∘ g → r ∘ f ≈ r ∘ g → f ≈ g) where

    universal : ∀ {X Y A B} (a : Hom Y A) (b : Hom Y B) (h : Hom X Y) {f g} →
                a ∘ h ≈ f → b ∘ h ≈ g → pair a b ∘ h ≈ pair f g
    universal a b h ef eg = ext _ _
      (transitive (symmetric (assoc l _ h)) (transitive (compose-cong (fst-law a b) reflexive) (transitive ef (symmetric (fst-law _ _)))))
      (transitive (symmetric (assoc r _ h)) (transitive (compose-cong (snd-law a b) reflexive) (transitive eg (symmetric (snd-law _ _)))))

    eta : ∀ {X A B} (h : Hom X (A ⊗ B)) → pair (l ∘ h) (r ∘ h) ≈ h
    eta h = ext _ _ (fst-law _ _) (snd-law _ _)

    right : ∀ {A B D} → Hom ((A ⊗ B) ⊗ D) (A ⊗ (B ⊗ D))
    right = pair (l ∘ l) (pair (r ∘ l) r)
    left : ∀ {A B D} → Hom (A ⊗ (B ⊗ D)) ((A ⊗ B) ⊗ D)
    left = pair (pair l (l ∘ r)) (r ∘ r)

    peek : ∀ {X A B D} (p : Hom B D) (q : Hom A B) (t : Hom X A) {u} → q ∘ t ≈ u → (p ∘ q) ∘ t ≈ p ∘ u
    peek p q t eq = transitive (assoc p q t) (compose-cong reflexive eq)

    unright : ∀ {A B D} → left {A} {B} {D} ∘ right ≈ identity
    unright = transitive (universal _ _ _
      (transitive (universal _ _ _ (fst-law _ _) (transitive (peek l r right (snd-law _ _)) (fst-law _ _))) (eta l))
      (transitive (peek r r right (snd-law _ _)) (snd-law _ _)))
      (ext _ _ (transitive (fst-law _ _) (symmetric (unitʳ l))) (transitive (snd-law _ _) (symmetric (unitʳ r))))

    unleft : ∀ {A B D} → right {A} {B} {D} ∘ left ≈ identity
    unleft = transitive (universal _ _ _
      (transitive (peek l l left (fst-law _ _)) (fst-law _ _))
      (transitive (universal _ _ _ (transitive (peek r l left (fst-law _ _)) (snd-law _ _)) (snd-law _ _)) (eta r)))
      (ext _ _ (transitive (fst-law _ _) (symmetric (unitʳ l))) (transitive (snd-law _ _) (symmetric (unitʳ r))))

    iso : ∀ A B D → Arrows.Inverse C (right {A} {B} {D})
    iso A B D = Arrows.inverse left unright unleft
