{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.ModularPairPull where

open import AoP.Chapter02.Categories
open import AoP.Chapter04.ProductAllegory using (Laws)

-- §5.2, (5.4). The left branch changes from A to B; the right
-- branch still lands in Y. The two product objects may differ.
module In {o h e p} {C : Category o h e} (L : Laws C p) where
  open Category C
  open Laws L
  private
    rid : ∀ {A B} {f : Hom A B} → f ⊑ f
    rid = respect reflexive
  module Step {A B Y P Q} (la : Hom P A) (ra : Hom P Y)
    (lb : Hom Q B) (rb : Hom Q Y) (r : Hom A B) (t : Hom P Q)
    -- Projection claims below are in the converse direction used by
    -- modularity. For products t represents r × id.
    (left : (rev lb ∘ r) ≈ (t ∘ rev la))
    (right : (rev t ∘ rev rb) ⊑ rev ra) where
    pull : ∀ {I} (x : Hom I A) (y : Hom I Y) →
      meet (rev lb ∘ (r ∘ x)) (rev rb ∘ y) ⊑ (t ∘ meet (rev la ∘ x) (rev ra ∘ y))
    pull x y = trans (glb (trans (lower₁ _ _) (respect align)) (lower₂ _ _))
      (trans (modular t (rev la ∘ x) (rev rb ∘ y)) (mono rid (glb (lower₁ _ _) (trans (lower₂ _ _) restrict))))
      where
        -- Put the left branch in the form t ∘ old-left, so the
        -- modular law can pull t outside the intersection.
        align : (rev lb ∘ (r ∘ x)) ≈ (t ∘ (rev la ∘ x))
        align = transitive (symmetric (assoc _ _ _)) (transitive (compose-cong left reflexive) (assoc _ _ _))
        -- The residual right branch produced by modularity is smaller
        -- than the old right branch, as required by monotonicity.
        restrict : (rev t ∘ (rev rb ∘ y)) ⊑ (rev ra ∘ y)
        restrict = trans (respect (symmetric (assoc _ _ _))) (mono right rid)
