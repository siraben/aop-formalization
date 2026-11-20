{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.AlgebraCategory where

open import Agda.Primitive using (_⊔_)
open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)

-- §2.6. An algebra interprets one layer of F. A homomorphism changes
-- the carrier while preserving that interpretation. Equality observes
-- the carrier arrow, so no equality of commuting-square proofs is needed.
module For {o h e} (C : Category o h e) (F : Functor C C) where
  open Category C
  private module F = Functor F
  record Algebra : Set (o ⊔ h) where
    constructor alg
    field carrier : Obj
          step : Hom (F.F₀ carrier) carrier
  open Algebra
  record Map (X Y : Algebra) : Set (h ⊔ e) where
    constructor hom
    field arrow : Hom (carrier X) (carrier Y)
          square : arrow ∘ step X ≈ step Y ∘ F.F₁ arrow
  open Map
  private
    infixr 2 _≈⟨_⟩_
    _≈⟨_⟩_ : ∀ {X Y} (p : Hom X Y) {q r} → p ≈ q → q ≈ r → p ≈ r
    _ ≈⟨ eq ⟩ rest = transitive eq rest
  -- Slide first f and then g past the constructor, and combine their
  -- layer actions using the functor composition law.
  paste : ∀ {X Y Z} (g : Map Y Z) (f : Map X Y) → Map X Z
  arrow (paste g f) = arrow g ∘ arrow f
  square (paste {X} {Y} {Z} g f) =
    (arrow g ∘ arrow f) ∘ step X ≈⟨ assoc _ _ _ ⟩
    arrow g ∘ (arrow f ∘ step X) ≈⟨ compose-cong reflexive (square f) ⟩
    arrow g ∘ (step Y ∘ F.F₁ (arrow f)) ≈⟨ symmetric (assoc _ _ _) ⟩
    (arrow g ∘ step Y) ∘ F.F₁ (arrow f) ≈⟨ compose-cong (square g) reflexive ⟩
    (step Z ∘ F.F₁ (arrow g)) ∘ F.F₁ (arrow f) ≈⟨ assoc _ _ _ ⟩
    step Z ∘ (F.F₁ (arrow g) ∘ F.F₁ (arrow f)) ≈⟨ compose-cong reflexive (symmetric (F.composition _ _)) ⟩
    reflexive
  algebras : Category _ _ _
  Category.Obj algebras = Algebra
  Category.Hom algebras = Map
  Category._≈_ algebras f g = arrow f ≈ arrow g
  Category.identity algebras = hom identity (transitive (unitˡ _) (transitive (symmetric (unitʳ _)) (compose-cong reflexive (symmetric F.identity))))
  Category._∘_ algebras = paste
  Category.reflexive algebras = reflexive
  Category.symmetric algebras = symmetric
  Category.transitive algebras = transitive
  Category.compose-cong algebras = compose-cong
  Category.unitˡ algebras f = unitˡ (arrow f)
  Category.unitʳ algebras f = unitʳ (arrow f)
  Category.assoc algebras g f k = assoc (arrow g) (arrow f) (arrow k)
