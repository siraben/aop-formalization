{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.RelatorLegAgreement where

open import Agda.Primitive using (_⊔_)
open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter04.ProductAllegory using (Laws)
open import AoP.Chapter04.AllegoryMapComposition using () renaming (module Law to Maps)
open import AoP.Chapter05.RelatorSpanConverse using (module Tables)

-- Corollary 5.1. Use a shared object action O so that the two arrow
-- images have comparable endpoints. Compare their values on each
-- arrow, without comparing records or requiring function extensionality.
module Compare {o h e p o′ h′ e′ q} {C : Category o h e} {D : Category o′ h′ e′}
  (L : Laws C p) (K : Laws D q) (O : Category.Obj C → Category.Obj D) where
  private module C = Category C
  private module D = Category D
  private module L = Laws L
  private module K = Laws K
  record Action : Set (o ⊔ h ⊔ e ⊔ p ⊔ h′ ⊔ e′ ⊔ q) where
    field image : ∀ {A B} → C.Hom A B → D.Hom (O A) (O B)
          resp : ∀ {A B} {r s : C.Hom A B} → r C.≈ s → image r D.≈ image s
          id-law : ∀ {A} → image (C.identity {A}) D.≈ D.identity
          comp : ∀ {A B E} (g : C.Hom B E) (f : C.Hom A B) → image (g C.∘ f) D.≈ (image g D.∘ image f)
          monotone : ∀ {A B} {r s : C.Hom A B} → r L.⊑ s → image r K.⊑ image s
    F : Functor C D
    F = record { F₀ = O; F₁ = image; resp = resp; identity = id-law; composition = comp }
    expand : ∀ {I A B} (f : C.Hom I B) (g : C.Hom I A) → Maps.Map L f → Maps.Map L g →
      (r : C.Hom A B) → r C.≈ (f C.∘ L.rev g) → image r D.≈ (image f D.∘ K.rev (image g))
    expand f g mf mg r table = D.transitive (resp table) (Tables.Monotone.Row.image L K F monotone f g mf mg)

  module Agreement (F G : Action) (maps : ∀ {A B} (f : C.Hom A B) → Maps.Map L f → Action.image F f D.≈ Action.image G f) where
    module F = Action F
    module G = Action G
    agree : ∀ {I A B} (f : C.Hom I B) (g : C.Hom I A) → Maps.Map L f → Maps.Map L g →
      (r : C.Hom A B) → r C.≈ (f C.∘ L.rev g) → F.image r D.≈ G.image r
    agree f g mf mg r table = D.transitive (F.expand f g mf mg r table)
      (D.transitive (D.compose-cong (maps f mf) turns) (D.symmetric (G.expand f g mf mg r table)))
      where
        turns = K.antisym (K.rev-mono (K.respect (maps g mg))) (K.rev-mono (K.respect (D.symmetric (maps g mg))))
