{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.ProductAssociator where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.FunctorIso using (module Arrows)

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

    cross : ∀ {A B X Y} → Hom A X → Hom B Y → Hom (A ⊗ B) (X ⊗ Y)
    cross f g = pair (f ∘ l) (g ∘ r)

    -- Both paths around the naturality square act separately on the
    -- three input coordinates. Normalize them to the same nested pair.
    natural : ∀ {A B D X Y Z} (f : Hom A X) (g : Hom B Y) (h : Hom D Z) →
              right ∘ cross (cross f g) h ≈ cross f (cross g h) ∘ right
    natural f g h = transitive route₁ (symmetric route₂)
      where
      pack = cross (cross f g) h
      normal = pair (f ∘ (l ∘ l)) (pair (g ∘ (r ∘ l)) (h ∘ r))
      first : (l ∘ l) ∘ pack ≈ f ∘ (l ∘ l)
      first = transitive (peek l l pack (fst-law _ _))
        (transitive (symmetric (assoc l (cross f g) l)) (transitive (compose-cong (fst-law _ _) reflexive) (assoc f l l)))
      middle : (r ∘ l) ∘ pack ≈ g ∘ (r ∘ l)
      middle = transitive (peek r l pack (fst-law _ _))
        (transitive (symmetric (assoc r (cross f g) l)) (transitive (compose-cong (snd-law _ _) reflexive) (assoc g r l)))
      route₁ : right ∘ pack ≈ normal
      route₁ = universal _ _ pack first (universal _ _ pack middle (snd-law _ _))
      tail : cross g h ∘ pair (r ∘ l) r ≈ pair (g ∘ (r ∘ l)) (h ∘ r)
      tail = universal _ _ _ (peek g l _ (fst-law _ _)) (peek h r _ (snd-law _ _))
      route₂ : cross f (cross g h) ∘ right ≈ normal
      route₂ = universal _ _ right (peek f l right (fst-law _ _))
        (transitive (peek (cross g h) r right (snd-law _ _)) tail)
