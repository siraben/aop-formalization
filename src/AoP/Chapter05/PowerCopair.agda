{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.PowerCopair where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter04.PowerTransposeTerminal using (module Slice)

-- §5.3. Fix the output O of both relations. Their transposes have a
-- common codomain P, so ordinary case analysis can select the fibre.
-- Following the selected fibre by membership retrieves its outputs.
module Into {o h e o′ h′ e′} (C : Category o h e) (D : Category o′ h′ e′)
  (J : Functor C D) (O : Category.Obj D) where
  private module C = Category C
  private module D = Category D
  private module J = Functor J
  module S = Slice C D J O
  module Build {P A B U} (member : D.Hom (J.F₀ P) O) (laws : S.Power.Laws P member)
    (i : C.Hom A U) (j : C.Hom B U)
    (R : D.Hom (J.F₀ A) O) (T : D.Hom (J.F₀ B) O) where
    module L = S.Power.Laws laws
    fibre = L.transpose
    module Cases (c : C.Hom U P)
      (left : (c C.∘ i) C.≈ fibre (S.obj A R)) (right : (c C.∘ j) C.≈ fibre (S.obj B T))
      (unique : ∀ f → (f C.∘ i) C.≈ fibre (S.obj A R) → (f C.∘ j) C.≈ fibre (S.obj B T) → f C.≈ c) where
      copair = member D.∘ J.F₁ c
      read : ∀ {X} (k : C.Hom X U) → (copair D.∘ J.F₁ k) D.≈ (member D.∘ J.F₁ (c C.∘ k))
      read k = D.transitive (D.assoc _ _ _) (D.compose-cong D.reflexive (D.symmetric (J.composition _ _)))
      first : (copair D.∘ J.F₁ i) D.≈ R
      first = D.transitive (read i) (D.transitive (D.compose-cong D.reflexive (J.resp left)) (L.cancel _))
      second : (copair D.∘ J.F₁ j) D.≈ T
      second = D.transitive (read j) (D.transitive (D.compose-cong D.reflexive (J.resp right)) (L.cancel _))
      -- Any solution's transpose satisfies the two ordinary case
      -- equations. Uniqueness there suffices to identify the relation.
      module Rival (t : D.Hom (J.F₀ U) O) where
        f = fibre (S.obj U t)
        branch : ∀ {X} (k : C.Hom X U) (s : D.Hom (J.F₀ X) O) → (t D.∘ J.F₁ k) D.≈ s → (f C.∘ k) C.≈ fibre (S.obj X s)
        branch k s eq = L.only _ _ (D.transitive (D.compose-cong D.reflexive (J.composition _ _))
          (D.transitive (D.symmetric (D.assoc _ _ _)) (D.transitive (D.compose-cong (L.cancel _) D.reflexive) eq)))
        only : (t D.∘ J.F₁ i) D.≈ R → (t D.∘ J.F₁ j) D.≈ T → t D.≈ copair
        only l r = D.transitive (D.symmetric (L.cancel _)) (D.compose-cong D.reflexive
          (J.resp (unique f (branch i R l) (branch j T r))))
