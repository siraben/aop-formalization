{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.RelatorDomainSpan where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter04.ProductAllegory using (Laws)
open import AoP.Chapter04.AllegoryMapComposition using () renaming (module Law to Maps)
open import AoP.Chapter05.SpanDomain using () renaming (module Law to Domain)
open import AoP.Chapter05.RelatorMapConverse using (module Lift)
open import AoP.Chapter05.RelatorSpanConverse using (module Tables)

-- Exercise 5.5: transport the row calculation rather than assuming
-- that F preserves intersections. The same input column computes the
-- domain in the source table and in the image span.
module Proof {o h e p o′ h′ e′ q} {C : Category o h e} {D : Category o′ h′ e′}
  (L : Laws C p) (K : Laws D q) (F : Functor C D)
  (mono : ∀ {A B} {r s : Category.Hom C A B} → Laws._⊑_ L r s → Laws._⊑_ K (Functor.F₁ F r) (Functor.F₁ F s)) where
  private module C = Category C
  private module D = Category D
  private module F = Functor F
  private module S = Domain L
  private module T = Domain K
  private module M = Lift.Monotone L K F mono
  private module P = Tables.Monotone L K F mono
  module Row {I A B} (f : C.Hom I B) (g : C.Hom I A) (mf : Maps.Map L f) (mg : Maps.Map L g) where
    module Before = S.Row f g (Maps.Map.entire mf) (Maps.Map.simple mg)
    module After = T.Row (F.F₁ f) (F.F₁ g) (Maps.Map.entire (M.On.functional f mf)) (Maps.Map.simple (M.On.functional g mg))
    preserve : (r : C.Hom A B) → r C.≈ Before.r → F.F₁ (S.dom r) D.≈ T.dom (F.F₁ r)
    preserve r eq = D.transitive (F.resp (C.transitive (S.congruent eq) Before.domain))
      (D.transitive (P.Row.image g g mg mg) (D.symmetric (D.transitive
        (T.congruent (D.transitive (F.resp eq) (P.Row.image f g mf mg))) After.domain)))
