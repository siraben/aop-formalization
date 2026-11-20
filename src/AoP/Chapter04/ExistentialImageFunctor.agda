{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.ExistentialImageFunctor where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter04.PowerTransposeTerminal using (module Slice)

-- §4.6. Given a representing membership arrow at each output object,
-- construct existential image by transposing R after membership. J
-- interprets functions in the relation category; the resulting functor
-- goes the other way. No powerset resizing is hidden in the construction.
module Build {o h e o′ h′ e′} (C : Category o h e) (D : Category o′ h′ e′)
  (J : Functor C D) (P : Category.Obj D → Category.Obj C)
  (mem : ∀ A → Category.Hom D (Functor.F₀ J (P A)) A) where
  private module C = Category C
  private module D = Category D
  module S A = Slice C D J A
  module U A = S.Power A (P A) (mem A)
  module Given (laws : ∀ A → U.Laws A) where
    module L A = U.Laws A (laws A)
    Λ : ∀ {X A} → D.Hom (Functor.F₀ J X) A → C.Hom X (P A)
    Λ {A = A} r = L.transpose A (S.obj _ r)
    E : ∀ {A B} → D.Hom A B → C.Hom (P A) (P B)
    E {A} r = Λ (r D.∘ mem A)
    -- To identify the composite, read its membership triangle. First
    -- cancel E r against membership, then cancel Λ s inside r.
    absorb : ∀ {X A B} (r : D.Hom A B) (s : D.Hom (Functor.F₀ J X) A) →
      (E r C.∘ Λ s) C.≈ Λ (r D.∘ s)
    absorb {X} {A} {B} r s = L.only B _ _ (D.transitive (D.compose-cong D.reflexive (Functor.composition J _ _))
      (D.transitive (D.symmetric (D.assoc _ _ _)) (D.transitive (D.compose-cong (L.cancel B _) D.reflexive)
      (D.transitive (D.assoc _ _ _) (D.compose-cong D.reflexive (L.cancel A _))))))
    congruent : ∀ {X A} {r s : D.Hom (Functor.F₀ J X) A} → r D.≈ s → Λ r C.≈ Λ s
    congruent {A = A} eq = L.only A _ _ (D.transitive (L.cancel A _) eq)
    image : Functor D C
    Functor.F₀ image = P
    Functor.F₁ image = E
    Functor.resp image eq = congruent (D.compose-cong eq D.reflexive)
    Functor.identity image {A} = C.transitive (congruent (D.unitˡ _)) (C.symmetric (U.Derived.reflection A (laws A)))
    Functor.composition image {A} g f = C.transitive (congruent (D.assoc _ _ _)) (C.symmetric (absorb g (f D.∘ mem A)))
