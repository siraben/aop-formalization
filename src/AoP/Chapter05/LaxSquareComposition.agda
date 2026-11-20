{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.LaxSquareComposition where

open import AoP.Chapter02.Categories
open import AoP.Chapter04.ProductAllegory using (Laws)

-- §5.7. When the two legs of a tabulation satisfy lax squares,
-- their composite satisfies one too. The component at the row object
-- appears only in the middle of the calculation and disappears again.
module Law {o h e p} {C : Category o h e} (L : Laws C p) where
  open Category C
  open Laws L
  paste : ∀ {A B I X Y J} (f : Hom I B) (g : Hom A I) (u : Hom J Y) (v : Hom X J)
    (a : Hom A X) (i : Hom I J) (b : Hom B Y) →
    (b ∘ f) ⊑ (u ∘ i) → (i ∘ g) ⊑ (v ∘ a) → (b ∘ (f ∘ g)) ⊑ ((u ∘ v) ∘ a)
  paste f g u v a i b first second = trans (respect (symmetric (assoc b f g)))
    (trans (mono first (respect reflexive)) (trans (respect (assoc u i g))
    (trans (mono (respect reflexive) second) (respect (symmetric (assoc u v a))))))
