{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.PartialGraphCoproduct where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter02.PartialGraphCategory using (Par; Partial; partial; module Partial)
open import AoP.Chapter02.TotalPartialEmbedding using (total)
open import AoP.Chapter02.OppositeCategory using (op)
open import AoP.Chapter02.SpanProduct using (module Over)
open import AoP.Chapter05.CopairCancellation using (copair)
open Partial

-- §2.5. A tagged input selects the branch before either partial graph
-- is consulted. Thus coproducts work without deciding definedness.
module Sum (A B : Set) where
  module S = Over (op Par) A B
  injections : S.Span
  injections = S.span (A ⊎ B) (total inl) (total inr)

  cases : ∀ {X} → Partial A X → Partial B X → Partial (A ⊎ B) X
  edge (cases f g) = copair (edge f) (edge g)
  single (cases f g) {inl a} = single f
  single (cases f g) {inr b} = single g

  -- The triangles of this cospan say that handling an injected input
  -- has exactly the graph of the corresponding branch. Conversely all
  -- inputs are tagged, so these two equations determine the handler.
  terminal : S.U.Terminal injections
  S.U.Terminal.enter terminal (S.span X f g) = S.via (cases f g)
    ((λ { (_ , (p , refl)) → p }) , (λ p → _ , (p , refl)))
    ((λ { (_ , (p , refl)) → p }) , (λ p → _ , (p , refl)))
  S.U.Terminal.unique terminal {S.span X f g} (S.via h (lf , lb) (rf , rb)) =
    (λ { {a = inl a} p → lf (_ , (p , refl)); {a = inr b} p → rf (_ , (p , refl)) }) ,
    (λ { {a = inl a} p → drop-tag (lb p); {a = inr b} p → drop-tag (rb p) })
    where drop-tag : ∀ {x tag} → Σ (A ⊎ B) (λ z → edge h x z × (tag ≡ z)) → edge h x tag
          drop-tag (_ , (q , refl)) = q
