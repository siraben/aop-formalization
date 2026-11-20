{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.RelatorMapConverse where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter04.ProductAllegory using (Laws)
open import AoP.Chapter04.AllegoryMapComposition using () renaming (module Law to Maps)
open import AoP.Chapter05.AllegoryAdjointConverse using () renaming (module Law to Adj)

-- Lemma 5.1: monotonicity transports the map unit and counit even
-- before we know whether F commutes with converse. Apply Prop. 4.1
-- only after transporting those inequalities into the target allegory.
module Lift {o h e p o′ h′ e′ q} {C : Category o h e} {D : Category o′ h′ e′}
  (L : Laws C p) (K : Laws D q) (F : Functor C D) where
  private module C = Category C
  private module D = Category D
  private module L = Laws L
  private module K = Laws K
  private module F = Functor F
  module Monotone (mono : ∀ {A B} {r s : C.Hom A B} → r L.⊑ s → F.F₁ r K.⊑ F.F₁ s) where
    module On {A B} (f : C.Hom A B) (map : Maps.Map L f) where
      open Maps.Map map
      unit = K.trans (K.respect (D.symmetric F.identity)) (K.trans (mono entire) (K.respect (F.composition _ _)))
      counit = K.trans (K.respect (D.symmetric (F.composition f (L.rev f)))) (K.trans (mono simple) (K.respect F.identity))
      module Image = Adj.Result K (F.F₁ f) (F.F₁ (L.rev f)) unit counit
      open Image public using (agreed; functional)
