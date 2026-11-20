{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.RelationalFoldTransfer where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter04.PowerTransposeTerminal using (module Slice)

-- §5.5, equation (5.12). J sends ordinary maps to relation arrows.
-- The lifting H on relations has object action F on represented types;
-- its extension law says H sends function graphs to the graph of Ff.
module Transfer {o h e o′ h′ e′} (C : Category o h e) (D : Category o′ h′ e′)
  (J : Functor C D) (F : Functor C C) where
  private module C = Category C
  private module D = Category D
  private module J = Functor J
  private module F = Functor F
  Rel : C.Obj → C.Obj → Set h′
  Rel X Y = D.Hom (J.F₀ X) (J.F₀ Y)
  module Lift (H : ∀ {X Y} → Rel X Y → Rel (F.F₀ X) (F.F₀ Y))
    (resp : ∀ {X Y} {r s : Rel X Y} → r D.≈ s → H r D.≈ H s)
    (compose : ∀ {X Y Z} (r : Rel Y Z) (s : Rel X Y) → H (r D.∘ s) D.≈ (H r D.∘ H s))
    (graph : ∀ {X Y} (f : C.Hom X Y) → H (J.F₁ f) D.≈ J.F₁ (F.F₁ f)) where
    module At {I B P} (roll : C.Hom (F.F₀ I) I) (r : Rel (F.F₀ B) B) (mem : Rel P B)
      (laws : Slice.Power.Laws C D J (J.F₀ B) P mem) where
      module S = Slice C D J (J.F₀ B)
      module L = S.Power.Laws laws
      -- Lift membership through one layer, run the relation algebra,
      -- then transpose to get an ordinary algebra on predicates.
      alg = L.transpose (S.obj (F.F₀ P) (r D.∘ H mem))
      read : ∀ {X} → C.Hom X P → Rel X B
      read f = mem D.∘ J.F₁ f
      route : ∀ {X Y} (f : C.Hom Y P) (g : C.Hom X Y) → read (f C.∘ g) D.≈ (read f D.∘ J.F₁ g)
      route f g = D.transitive (D.compose-cong D.reflexive (J.composition _ _)) (D.symmetric (D.assoc _ _ _))
      layer : ∀ {X} (f : C.Hom X P) → read (alg C.∘ F.F₁ f) D.≈ (r D.∘ H (read f))
      layer f = D.transitive (route alg _) (D.transitive (D.compose-cong (L.cancel _) (D.symmetric (graph f)))
        (D.transitive (D.assoc _ _ _) (D.compose-cong D.reflexive (D.symmetric (compose mem _)))))
      module Fold (fold : C.Hom I P) (step : (fold C.∘ roll) C.≈ (alg C.∘ F.F₁ fold))
        (unique : ∀ f → (f C.∘ roll) C.≈ (alg C.∘ F.F₁ f) → f C.≈ fold) where
        solution = read fold
        solves : (solution D.∘ J.F₁ roll) D.≈ (r D.∘ H solution)
        solves = D.transitive (D.symmetric (route fold roll)) (D.transitive (D.compose-cong D.reflexive (J.resp step)) (layer fold))
        module Rival (x : Rel I B) (eq : (x D.∘ J.F₁ roll) D.≈ (r D.∘ H x)) where
          f = L.transpose (S.obj I x)
          -- Both candidate functions represent the same relation;
          -- transpose uniqueness turns the read-back equality into
          -- the ordinary fold equation, to which initiality applies.
          square : read (f C.∘ roll) D.≈ read (alg C.∘ F.F₁ f)
          square = D.transitive (route f roll) (D.transitive (D.compose-cong (L.cancel _) D.reflexive)
            (D.transitive eq (D.transitive (D.compose-cong D.reflexive (resp (D.symmetric (L.cancel _)))) (D.symmetric (layer f)))))
          eilenberg-wright : f C.≈ fold
          eilenberg-wright = unique f (C.transitive (L.only _ _ square) (C.symmetric (L.only _ _ D.reflexive)))
          only : x D.≈ solution
          only = D.transitive (D.symmetric (L.cancel _)) (D.compose-cong D.reflexive (J.resp eilenberg-wright))

        -- Eilenberg–Wright: transposing the relational fold yields the
        -- ordinary fold on fibres. Expose the equation for any lawful
        -- implementation, including the solution constructed above.
        transpose-fold : (x : Rel I B) → (x D.∘ J.F₁ roll) D.≈ (r D.∘ H x) → L.transpose (S.obj I x) C.≈ fold
        transpose-fold = Rival.eilenberg-wright
