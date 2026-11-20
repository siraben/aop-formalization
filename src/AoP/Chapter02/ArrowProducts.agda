{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.ArrowProducts where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.ArrowCategory using (module Arrows)
open import Agda.Builtin.Sigma using (fst; snd; _,_)

-- Exercise 2.29. Pair the sources and the targets separately. The
-- product edge maps the two coordinates by the two given edges. A cone
-- of squares then pairs coordinatewise too; use the two projections to
-- check that the resulting pair of maps really is a commuting square.
module Construction {o h e} (C : Category o h e) where
  open Category C
  open Arrows C
  open Arrow
  open Square
  module Products (_⊗_ : Obj → Obj → Obj)
    (l : ∀ {A B} → Hom (A ⊗ B) A) (r : ∀ {A B} → Hom (A ⊗ B) B)
    (pair : ∀ {X A B} → Hom X A → Hom X B → Hom X (A ⊗ B))
    (pl : ∀ {X A B} (a : Hom X A) (b : Hom X B) → l ∘ pair a b ≈ a)
    (pr : ∀ {X A B} (a : Hom X A) (b : Hom X B) → r ∘ pair a b ≈ b)
    (ext : ∀ {X A B} (f g : Hom X (A ⊗ B)) → l ∘ f ≈ l ∘ g → r ∘ f ≈ r ∘ g → f ≈ g) where
    product : Arrow → Arrow → Arrow
    product f g = arrow _ _ (pair (edge f ∘ l) (edge g ∘ r))
    projL : ∀ f g → Square (product f g) f
    projL f g = box l l (symmetric (pl _ _))
    projR : ∀ f g → Square (product f g) g
    projR f g = box r r (symmetric (pr _ _))

    observe : ∀ {X Y Z W} (p : Hom Z W) (s : Hom Y Z) (t : Hom X Y) {v} → p ∘ s ≈ v → p ∘ (s ∘ t) ≈ v ∘ t
    observe p s t eq = transitive (symmetric (assoc p s t)) (compose-cong eq reflexive)

    pack : ∀ {x f g} → Square x f → Square x g → Square x (product f g)
    pack {x} {f} {g} a b = box top′ bottom′ (ext _ _ first second)
      where
      top′ = pair (top a) (top b)
      bottom′ = pair (bottom a) (bottom b)
      first = transitive (observe l _ top′ (pl _ _)) (transitive (assoc (edge f) l top′)
        (transitive (compose-cong reflexive (pl _ _)) (transitive (commutes a) (symmetric (observe l bottom′ (edge x) (pl _ _))))))
      second = transitive (observe r _ top′ (pr _ _)) (transitive (assoc (edge g) r top′)
        (transitive (compose-cong reflexive (pr _ _)) (transitive (commutes b) (symmetric (observe r bottom′ (edge x) (pr _ _))))))

    module A = Category Arr
    left-law : ∀ {x f g} (a : Square x f) (b : Square x g) → paste (projL f g) (pack a b) A.≈ a
    left-law a b = pl _ _ , pl _ _
    right-law : ∀ {x f g} (a : Square x f) (b : Square x g) → paste (projR f g) (pack a b) A.≈ b
    right-law a b = pr _ _ , pr _ _
    unique : ∀ {x f g} (a b : Square x (product f g)) → paste (projL f g) a A.≈ paste (projL f g) b →
             paste (projR f g) a A.≈ paste (projR f g) b → a A.≈ b
    unique a b (p , q) (s , t) = ext _ _ p s , ext _ _ q t
