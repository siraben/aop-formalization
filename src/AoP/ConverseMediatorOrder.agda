{-# OPTIONS --safe --without-K #-}
module AoP.ConverseMediatorOrder where

open import AoP.Categories
open import AoP.Functors using (Functor)
open import AoP.ProductAllegory using (Laws)

-- Theorem 5.1, reverse calculation with its local simplicity premise.
-- A comparison of tabulations presents the smaller span by running
-- both legs of the larger one after a common change of rows m.
module Proof {o h e p o′ h′ e′ q} {C : Category o h e} {D : Category o′ h′ e′}
  (L : Laws C p) (K : Laws D q) (F : Functor C D)
  (converse : ∀ {A B} (r : Category.Hom C A B) → Category._≈_ D (Functor.F₁ F (Laws.rev L r)) (Laws.rev K (Functor.F₁ F r))) where
  private module C = Category C
  private module D = Category D
  private module L = Laws L
  private module K = Laws K
  private module F = Functor F
  private
    rid : ∀ {A B} {r : D.Hom A B} → r K.⊑ r
    rid = K.respect D.reflexive
    turn : ∀ {A B} {r s : D.Hom A B} → r D.≈ s → K.rev r D.≈ K.rev s
    turn eq = K.antisym (K.rev-mono (K.respect eq)) (K.rev-mono (K.respect (D.symmetric eq)))
  module At {I J A B} (f : C.Hom J B) (g : C.Hom J A) (m : C.Hom I J) where
    small = (f C.∘ m) C.∘ L.rev (g C.∘ m)
    large = f C.∘ L.rev g
    -- Expose the two copies of the row change in the lifted span.
    expose : F.F₁ small D.≈ ((F.F₁ f D.∘ F.F₁ m) D.∘ (K.rev (F.F₁ m) D.∘ K.rev (F.F₁ g)))
    expose = D.transitive (F.composition _ _) (D.compose-cong (F.composition _ _)
      (D.transitive (converse _) (D.transitive (turn (F.composition _ _)) (K.flip _ _))))
    contract : (F.F₁ m D.∘ K.rev (F.F₁ m)) K.⊑ D.identity → F.F₁ small K.⊑ F.F₁ large
    contract simple = K.trans (K.respect expose) (K.trans (K.respect (D.assoc _ _ _))
      (K.mono rid (K.trans (K.respect (D.symmetric (D.assoc _ _ _))) (K.trans (K.mono simple rid)
        (K.respect (D.unitˡ _))))) )
      -- Fold back the larger table's image.
      |> finish
      where
        finish : F.F₁ small K.⊑ (F.F₁ f D.∘ K.rev (F.F₁ g)) → F.F₁ small K.⊑ F.F₁ large
        finish le = K.trans le (K.respect (D.symmetric (D.transitive (F.composition _ _) (D.compose-cong D.reflexive (converse g)))))
        _|>_ : ∀ {x y : Set q} → x → (x → y) → y
        a |> k = k a
