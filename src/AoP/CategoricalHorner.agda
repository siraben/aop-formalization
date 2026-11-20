{-# OPTIONS --safe --without-K #-}
module AoP.CategoricalHorner where

open import AoP.Categories
open import AoP.Functors using (Functor)
open import AoP.Transformations using (Natural)
open import AoP.AlgebraCategory using (module For)
open import AoP.InitialAlgebraFolds using (module From)
open import AoP.ChangeAlgebraParameter using (module Change)
open import AoP.ParametricFoldSquare using (module Square)

-- Exercise 3.11. Building the triangle relabels its children before
-- attaching the constructor. After reduction, that relabelling may be
-- replaced by a change h of the reduced result, if promotion holds.
module Rule {o h e} (C : Category o h e) (F : Functor C C) (shift : Natural F F) where
  open Category C
  module F = Functor F
  open For C F
  module Given {I} (i : From.U.Initial C F I) (B : Algebra) where
    open From.Laws C F i
    open Algebra
    module M = Change.Fold C shift i i
    tri = alg (carrier I) (step I ∘ F.F₁ M.relabel)
    module Reduce (h : Hom (carrier B) (carrier B))
      (law : h ∘ step B ≈ (step B ∘ Natural.η shift (carrier B)) ∘ F.F₁ h) where
      target = alg (carrier B) (step B ∘ F.F₁ h)
      promote = Square.Proof.commute C shift i i B B h law
      -- Compute one triangle layer, merge the two mapped arrows, use
      -- promotion inside F, and split the resulting composite again.
      square : fold B ∘ step tri ≈ step target ∘ F.F₁ (fold B)
      square =
        fold B ∘ (step I ∘ F.F₁ M.relabel) ≈⟨ symmetric (assoc _ _ _) ⟩
        (fold B ∘ step I) ∘ F.F₁ M.relabel ≈⟨ compose-cong (computation B) reflexive ⟩
        (step B ∘ F.F₁ (fold B)) ∘ F.F₁ M.relabel ≈⟨ assoc _ _ _ ⟩
        step B ∘ (F.F₁ (fold B) ∘ F.F₁ M.relabel) ≈⟨ under (symmetric (F.composition _ _)) ⟩
        step B ∘ F.F₁ (fold B ∘ M.relabel) ≈⟨ under (F.resp (symmetric promote)) ⟩
        step B ∘ F.F₁ (h ∘ fold B) ≈⟨ under (F.composition _ _) ⟩
        step B ∘ (F.F₁ h ∘ F.F₁ (fold B)) ≈⟨ symmetric (assoc _ _ _) ⟩
        reflexive
        where
        infixr 2 _≈⟨_⟩_
        _≈⟨_⟩_ : ∀ {X Y} (p : Hom X Y) {q r} → p ≈ q → q ≈ r → p ≈ r
        _ ≈⟨ eq ⟩ rest = transitive eq rest
        under : ∀ {X} {p q : Hom X (F.F₀ (carrier B))} → p ≈ q → step B ∘ p ≈ step B ∘ q
        under = compose-cong reflexive
      horner : fold B ∘ fold tri ≈ fold target
      horner = fusion (hom (fold B) square)
