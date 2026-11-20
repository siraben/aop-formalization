{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.TabularIndirectEquality where

open import Agda.Primitive using (Level)
open import AoP.Chapter02.Categories
open import AoP.Chapter04.ProductAllegory using (Laws)

-- §4.6. To compare two relations indirectly, the test arrows need
-- only be spans of maps. Tabulating an arbitrary test recovers it
-- as f ∘ g˘. For equality it suffices to tabulate each side in turn.
module Law {o h e p} {C : Category o h e} (L : Laws C p) where
  open Category C
  open Laws L
  module Test {m : Level} (Map : ∀ {A B} → Hom A B → Set m) {A B : Obj} where
    record Factor (X : Hom A B) : Set (o Agda.Primitive.⊔ h Agda.Primitive.⊔ m Agda.Primitive.⊔ e) where
      field rows : Obj
            target : Hom rows B
            source : Hom rows A
            target-map : Map target
            source-map : Map source
            reads : (target ∘ rev source) ≈ X
    SpanTests : Hom A B → Hom A B → Set _
    SpanTests X Y = ∀ {T} (f : Hom T B) (g : Hom T A) → Map f → Map g → (f ∘ rev g) ⊑ X → (f ∘ rev g) ⊑ Y

    -- Joint monicity is needed for a *unique* table mediator. To
    -- detect inclusion only the factor equation and map legs matter.
    detect : ∀ {X Y} → Factor X → SpanTests X Y → X ⊑ Y
    detect fact test = trans (respect (symmetric reads)) (test target source target-map source-map (respect reads))
      where open Factor fact
    equality : ∀ {X Y} → Factor X → Factor Y → SpanTests X Y → SpanTests Y X → X ≈ Y
    equality x y to from = antisym (detect x to) (detect y from)
