{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.AbstractFoldRetraction where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.InitialAlgebraFolds using (module From)
open import AoP.Chapter02.AlgebraCategory using (module For)

-- Exercises 2.34–2.36. Work with arrow equality in the base category.
module Derive {o h e} (C : Category o h e) (F : Functor C C) where
  open Category C
  open For C F
  module F = Functor F
  module Laws {I} (i : From.U.Initial C F I) where
    open From.Laws C F i
    T = Algebra.carrier I
    inn = Algebra.step I
    module Section {A} (m : Hom T A) (undo : Hom A T) (cancel : undo ∘ m ≈ identity) where
      -- Undo each child, apply the old constructor, then encode again.
      target = alg A ((m ∘ inn) ∘ F.F₁ undo)
      children : F.F₁ undo ∘ F.F₁ m ≈ identity
      children = transitive (symmetric (F.composition undo m)) (transitive (F.resp cancel) F.identity)
      as-fold : m ≈ fold target
      as-fold = unique target m (symmetric (transitive (assoc _ _ _) (transitive (compose-cong reflexive children) (unitʳ _))))

    slide : ∀ {A B} (f : Hom A B) (g : Hom (F.F₀ B) A) → fold (alg B (f ∘ g)) ≈ f ∘ fold (alg A (g ∘ F.F₁ f))
    slide f g = symmetric (fusion (hom f (symmetric (assoc _ _ _))))

    -- In a product of A and T, the pairing of f with identity records
    -- the result alongside the original subtree. Only its projection
    -- equations are needed; the right one gives the section above.
    module Remember {A P} (f : Hom T A) (save : Hom T P) (left : Hom P A) (right : Hom P T)
      (read : left ∘ save ≈ f) (restore : right ∘ save ≈ identity) where
      module S = Section save right restore
      projected : f ≈ left ∘ fold S.target
      projected = transitive (symmetric read) (compose-cong reflexive S.as-fold)
