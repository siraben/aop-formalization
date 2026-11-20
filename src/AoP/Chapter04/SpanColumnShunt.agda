{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.SpanColumnShunt where

open import AoP.Chapter02.Categories
open import AoP.Chapter04.ProductAllegory using (Laws)

-- §4.6. A table row map g is entire and simple. These two inequalities
-- move its converse from the left of an inclusion to g on the right.
-- This is the step that turns a test on a span into a test on columns.
module Law {o h e p} {C : Category o h e} (L : Laws C p) where
  open Category C
  open Laws L
  private
    rid : ∀ {X Y} {f : Hom X Y} → f ⊑ f
    rid = respect reflexive
  module Move {I B} (g : Hom I B) (unit : identity ⊑ (rev g ∘ g)) (counit : (g ∘ rev g) ⊑ identity) where
    across : ∀ {Z} (a : Hom I Z) (b : Hom B Z) → (a ∘ rev g) ⊑ b → a ⊑ (b ∘ g)
    across a b sub = trans (respect (symmetric (unitʳ a))) (trans (mono rid unit)
      (trans (respect (symmetric (assoc a _ g))) (mono sub rid)))
    back : ∀ {Z} (a : Hom I Z) (b : Hom B Z) → a ⊑ (b ∘ g) → (a ∘ rev g) ⊑ b
    back a b sub = trans (mono sub rid) (trans (respect (assoc b g _)) (trans (mono rid counit) (respect (unitʳ b))))

    -- In particular the test mem ∘ (f ∘ g˘) ⊑ R compares the member
    -- column at f with the relation column at g, on the same row.
    column : ∀ {P A} (mem : Hom P A) (f : Hom I P) (R : Hom B A) →
      (mem ∘ (f ∘ rev g)) ⊑ R → (mem ∘ f) ⊑ (R ∘ g)
    column mem f R bound = across _ _ (trans (respect (assoc mem f _)) bound)
    span : ∀ {P A} (mem : Hom P A) (f : Hom I P) (R : Hom B A) →
      (mem ∘ f) ⊑ (R ∘ g) → (mem ∘ (f ∘ rev g)) ⊑ R
    span mem f R bound = trans (respect (symmetric (assoc mem f _))) (back _ _ bound)
