{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.LaxTabulationTheorem where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter04.ProductAllegory using (Laws)
open import AoP.Chapter04.AllegoryMapComposition using () renaming (module Law to Maps)
open import AoP.Chapter05.RelatorSpanConverse using (module Tables)
open import AoP.Chapter05.LaxMapSquare using (module Square)
open import AoP.Chapter05.LaxSquareComposition using () renaming (module Law to Squares)

-- Theorem 5.2. Neither direction requires the components to be maps.
-- Use f for the source-side lifting of an arrow and g for the target
-- side of the square. The naturality equation compares their images
-- after composing with the component on the appropriate side.
module Theorem {o h e p o′ h′ e′ q} {C : Category o h e} {D : Category o′ h′ e′}
  (L : Laws C p) (K : Laws D q) (F G : Functor C D) where
  private module C = Category C
  private module D = Category D
  private module L = Laws L
  private module K = Laws K
  private module F = Functor F
  private module G = Functor G
  module Proof (fm : ∀ {A B} {r s : C.Hom A B} → r L.⊑ s → F.F₁ r K.⊑ F.F₁ s)
    (gm : ∀ {A B} {r s : C.Hom A B} → r L.⊑ s → G.F₁ r K.⊑ G.F₁ s)
    (η : ∀ A → D.Hom (F.F₀ A) (G.F₀ A)) where
    module P = Tables.Monotone L K F fm
    module Q = Tables.Monotone L K G gm
    Lax : ∀ {A B} → C.Hom A B → Set q
    Lax {A} {B} r = (η B D.∘ F.F₁ r) K.⊑ (G.F₁ r D.∘ η A)
    Natural : ∀ {A B} → C.Hom A B → Set e′
    Natural {A} {B} r = (G.F₁ r D.∘ η A) D.≈ (η B D.∘ F.F₁ r)
    module Leg {A B} (r : C.Hom A B) (map : Maps.Map L r) where
      module S = Square.At K (F.F₁ r) (G.F₁ r) (η A) (η B) (P.M.On.functional r map) (Q.M.On.functional r map)
      exact : Lax r → Lax (L.rev r) → Natural r
      exact direct back = S.exact direct (K.trans (K.mono (K.respect D.reflexive) (K.respect (D.symmetric (P.M.On.agreed r map))))
        (K.trans back (K.mono (K.respect (Q.M.On.agreed r map)) (K.respect D.reflexive))))
    module Row {I A B} (f : C.Hom I B) (g : C.Hom I A) (mf : Maps.Map L f) (mg : Maps.Map L g) where
      -- Expand both functors on the same table; naturality on its first
      -- leg goes forward, while the second leg's square is shunted.
      extend : (r : C.Hom A B) → r C.≈ (f C.∘ L.rev g) → Natural f → Natural g → Lax r
      extend r eq nf ng = K.trans (K.mono (K.respect D.reflexive) (K.respect (D.transitive (F.resp eq) (P.Row.image f g mf mg))))
        (K.trans (Squares.paste K _ _ _ _ (η A) (η I) (η B) (K.respect (D.symmetric nf)) (Leg.S.turn g mg (K.respect ng)))
        (K.mono (K.respect (D.symmetric (D.transitive (G.resp eq) (Q.Row.image f g mf mg)))) (K.respect D.reflexive)))
