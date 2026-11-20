{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.GeneralHorner where

open import AoP.Common.Prelude
open import AoP.Chapter02.Categories using (Fun)
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.Initial using (module Theory)
open import AoP.Chapter02.ParametricFold using (module Parameters)

-- Exercise 3.11. Transforming the elements of a layer (shift) and
-- transforming its recursive slots (map) commute. A triangle applies
-- the induced element map to each child before attaching its parent.
-- The efficient fold instead applies h to each *reduced* child.
module Rule (F : Functor Fun Fun) (I : Theory.Initial F) where
  open Functor F renaming (F₀ to Layer; F₁ to map)
  open Theory.Initial I
  open Theory.Laws F I using (fusion)
  module Transform (shift : ∀ {X} → Layer X → Layer X)
                   (natural : ∀ {X Y} (u : X → Y) t → map u (shift t) ≡ shift (map u t)) where
    relabel : μ → μ
    relabel = ⦅ (λ t → inn (shift t)) ⦆
    triangle : μ → μ
    triangle = ⦅ (λ t → inn (map relabel t)) ⦆

    module Reduce {B : Set} (g : Layer B → B) (h : B → B)
                  (square : ∀ t → h (g t) ≡ g (shift (map h t))) where
      -- Exercise 2.39 gives promotion when both parameter types agree.
      module P = Parameters.Square (λ (_ : Set) → F) (λ _ → I) {⊤} {⊤} shift natural g g h square
      promote : ∀ x → h (⦅ g ⦆ x) ≡ ⦅ g ⦆ (relabel x)
      promote = P.commute

      private
        back : ∀ {X : Set} {a b : X} → a ≡ b → b ≡ a
        back refl = refl
      horner : ∀ x → ⦅ g ⦆ (triangle x) ≡ ⦅ (λ t → g (map h t)) ⦆ x
      horner = fusion _ _ ⦅ g ⦆ λ t → begin
        ⦅ g ⦆ (inn (map relabel t)) ≡⟨ computation g _ ⟩
        g (map ⦅ g ⦆ (map relabel t)) ≡⟨ cong g (back (composition ⦅ g ⦆ relabel t)) ⟩
        g (map (λ x → ⦅ g ⦆ (relabel x)) t) ≡⟨ cong g (resp (λ x → back (promote x)) t) ⟩
        g (map (λ x → h (⦅ g ⦆ x)) t) ≡⟨ cong g (composition h ⦅ g ⦆ t) ⟩
        g (map h (map ⦅ g ⦆ t)) ∎
