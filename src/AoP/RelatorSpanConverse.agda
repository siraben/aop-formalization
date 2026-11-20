{-# OPTIONS --safe --without-K #-}
module AoP.RelatorSpanConverse where

open import AoP.Categories
open import AoP.Functors using (Functor)
open import AoP.ProductAllegory using (Laws)
open import AoP.AllegoryMapComposition using () renaming (module Law to Maps)
open import AoP.RelatorMapConverse using (module Lift)

-- Theorem 5.1, forward implication. A table represents a relation by
-- two maps out of its row object. Reversing the relation swaps those
-- maps; the functor's action on maps is enough to compare the results.
module Tables {o h e p o′ h′ e′ q} {C : Category o h e} {D : Category o′ h′ e′}
  (L : Laws C p) (K : Laws D q) (F : Functor C D) where
  private module C = Category C
  private module D = Category D
  private module L = Laws L
  private module K = Laws K
  private module F = Functor F
  private
    source-rev : ∀ {A B} {r s : C.Hom A B} → r C.≈ s → L.rev r C.≈ L.rev s
    source-rev eq = L.antisym (L.rev-mono (L.respect eq)) (L.rev-mono (L.respect (C.symmetric eq)))
    target-rev : ∀ {A B} {r s : D.Hom A B} → r D.≈ s → K.rev r D.≈ K.rev s
    target-rev eq = K.antisym (K.rev-mono (K.respect eq)) (K.rev-mono (K.respect (D.symmetric eq)))
  module Monotone (mono : ∀ {A B} {r s : C.Hom A B} → r L.⊑ s → F.F₁ r K.⊑ F.F₁ s) where
    module M = Lift.Monotone L K F mono
    module Row {I A B} (f : C.Hom I B) (g : C.Hom I A) (mf : Maps.Map L f) (mg : Maps.Map L g) where
      swap : L.rev (f C.∘ L.rev g) C.≈ (g C.∘ L.rev f)
      swap = C.transitive (L.flip _ _) (C.compose-cong (L.invol _) C.reflexive)
      image : F.F₁ (f C.∘ L.rev g) D.≈ (F.F₁ f D.∘ K.rev (F.F₁ g))
      image = D.transitive (F.composition _ _) (D.compose-cong D.reflexive (M.On.agreed g mg))
      reverse-image : K.rev (F.F₁ (f C.∘ L.rev g)) D.≈ (F.F₁ g D.∘ K.rev (F.F₁ f))
      reverse-image = D.transitive (target-rev image) (D.transitive (K.flip _ _) (D.compose-cong (K.invol _) D.reflexive))
      preserve : (r : C.Hom A B) → r C.≈ (f C.∘ L.rev g) → F.F₁ (L.rev r) D.≈ K.rev (F.F₁ r)
      preserve r table = D.transitive (F.resp (C.transitive (source-rev table) swap))
        (D.transitive (F.composition _ _) (D.transitive (D.compose-cong D.reflexive (M.On.agreed f mf))
        (D.symmetric (D.transitive (target-rev (F.resp table)) reverse-image))))
