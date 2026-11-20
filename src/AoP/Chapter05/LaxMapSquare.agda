{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.LaxMapSquare where

open import AoP.Chapter02.Categories
open import AoP.Chapter04.ProductAllegory using (Laws)
open import AoP.Chapter04.AllegoryMapComposition using () renaming (module Law to Maps)
open import AoP.Chapter04.SpanColumnShunt using () renaming (module Law to Shunt)

-- §5.7, Theorem 5.2. The missing inclusion on a function square is
-- exactly the lax inclusion on its converse. Let f and g be the two
-- images of the function, and p and q the components at its endpoints.
-- Only f and g must be maps; the components may be arbitrary arrows.
module Square {o h e k} {C : Category o h e} (L : Laws C k) where
  open Category C
  open Laws L
  private
    rid : ∀ {A B} {r : Hom A B} → r ⊑ r
    rid = respect reflexive
  module At {A B X Y} (f : Hom A B) (g : Hom X Y) (p : Hom A X) (q : Hom B Y)
    (mf : Maps.Map L f) (mg : Maps.Map L g) where
    module F = Shunt.Move L f (Maps.Map.entire mf) (Maps.Map.simple mf)
    -- Insert the unit of g, move across the given square, and shunt
    -- f to the other side. The reverse calculation uses the counit.
    turn : (g ∘ p) ⊑ (q ∘ f) → (p ∘ rev f) ⊑ (rev g ∘ q)
    turn sub = F.back _ _ (trans (respect (symmetric (unitˡ p)))
      (trans (mono (Maps.Map.entire mg) rid) (trans (respect (assoc _ _ _))
      (trans (mono rid sub) (respect (symmetric (assoc _ _ _)))))))
    back : (p ∘ rev f) ⊑ (rev g ∘ q) → (g ∘ p) ⊑ (q ∘ f)
    back sub = trans (mono rid (F.across _ _ sub)) (trans (respect (symmetric (assoc _ _ _)))
      (mono (trans (respect (symmetric (assoc _ _ _))) (trans (mono (Maps.Map.simple mg) rid) (respect (unitˡ q)))) rid))
    exact : (q ∘ f) ⊑ (g ∘ p) → (p ∘ rev f) ⊑ (rev g ∘ q) → (g ∘ p) ≈ (q ∘ f)
    exact direct reverse = antisym (back reverse) direct
