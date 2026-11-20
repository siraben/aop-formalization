{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.ParametricFold where

open import AoP.Common.Prelude
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.Categories using (Fun)
open import AoP.Chapter02.Initial using (module Theory)

-- Exercise 2.39 in Fun. For a fixed parameter, F acts on the recursive
-- argument as an ordinary functor. A map of parameters changes one
-- layer by a natural transformation. Fold uniqueness lets us compare
-- the two ways of relabelling an entire folded value.
module Parameters (F : Set → Functor Fun Fun)
                  (I : ∀ P → Theory.Initial (F P)) where
  open Functor using (F₀; F₁)
  module T (P : Set) = Theory.Initial (I P)

  module Square {P Q A B : Set}
    (shift : ∀ {X} → F₀ (F P) X → F₀ (F Q) X)
    (natural : ∀ {X Y} (h : X → Y) t → F₁ (F Q) h (shift t) ≡ shift (F₁ (F P) h t))
    (a : F₀ (F P) A → A) (b : F₀ (F Q) B → B) (h : A → B)
    (algebra-square : ∀ t → h (a t) ≡ b (shift (F₁ (F P) h t))) where

    -- Mapping the parameter is itself a fold into the new carrier.
    relabel : T.μ P → T.μ Q
    relabel = T.⦅_⦆ P (λ t → T.inn Q (shift t))

    commute : ∀ x → h (T.⦅_⦆ P a x) ≡ T.⦅_⦆ Q b (relabel x)
    commute x = begin
      h (T.⦅_⦆ P a x) ≡⟨ fuse a _ h algebra-square x ⟩
      T.⦅_⦆ P (λ t → b (shift t)) x ≡⟨ back (fuse _ _ (T.⦅_⦆ Q b) step x) ⟩
      T.⦅_⦆ Q b (relabel x) ∎
      where
      open Theory.Laws (F P) (I P) renaming (fusion to fuse)
      back : ∀ {X : Set} {u v : X} → u ≡ v → v ≡ u
      back refl = refl
      step : ∀ t → T.⦅_⦆ Q b (T.inn Q (shift t)) ≡ b (shift (F₁ (F P) (T.⦅_⦆ Q b) t))
      step t = T.computation Q b (shift t) ∙ cong b (natural (T.⦅_⦆ Q b) t)
