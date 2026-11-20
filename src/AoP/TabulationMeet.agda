{-# OPTIONS --safe --without-K #-}
module AoP.TabulationMeet where

open import AoP.Prelude
open import AoP.Relations using (_←_; _∘_; _⊓_; _˘; _⊆_)
open import AoP.Shunting using (graph; Map)
open import AoP.TabulationMediator using (module Table)

-- Proposition 4.2, the intermediate relation in the calculation. Match
-- a candidate row against each observed column, then intersect the two
-- tests. Joint monicity makes this relation single-valued, even if some
-- inputs have no matching row. Inclusion in the table gives totality.
module Match {A B T D : Set} (f : T → B) (g : T → A) (h : D → B) (k : D → A)
  (joint : ∀ x y → f x ≡ f y → g x ≡ g y → x ≡ y) where
  M : T ← D
  M = (graph f ˘ ∘ graph h) ⊓ (graph g ˘ ∘ graph k)
  private
    back : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
    back refl = refl
  columns : ∀ {t d} → M t d → (f t ≡ h d) × (g t ≡ k d)
  columns ((b , p , q) , (a , r , s)) = (p ∙ back q) , (r ∙ back s)
  match : ∀ {t d} → f t ≡ h d → g t ≡ k d → M t d
  match p q = (_ , p , refl) , (_ , q , refl)
  single : ∀ {t u d} → M t d → M u d → t ≡ u
  single p q = joint _ _ (fst (columns p) ∙ back (fst (columns q))) (snd (columns p) ∙ back (snd (columns q)))

  module Included (R : B ← A) (find : R ⊆ graph f ∘ graph g ˘) (read : graph f ∘ graph g ˘ ⊆ R)
    (incl : graph h ∘ graph k ˘ ⊆ R) where
    module S = Table.Span R f g find read joint h k
    m = S.factor incl
    hits : ∀ d → M (S.Mediator.row m d) d
    hits d = match (S.Mediator.target m d) (S.Mediator.source m d)
    function : Map M
    Map.entire function {a = d} refl = _ , hits d , hits d
    Map.simple function (_ , p , q) = single p q
    graph-in : graph (S.Mediator.row m) ⊆ M
    graph-in {a = d} refl = hits d
    graph-out : M ⊆ graph (S.Mediator.row m)
    graph-out {a = d} p = single (hits d) p
