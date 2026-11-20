{-# OPTIONS --safe --without-K #-}
module AoP.RelSumProduct where

open import AoP.Prelude
open import AoP.Polynomial using (_⊎_; inl; inr)
open import AoP.Relations using (_˘)
open import AoP.RelationGraphCategory using (Rel)
open import AoP.Shunting using (graph)
open import AoP.SpanProduct using (module Over)
open import AoP.CopairCancellation using (copair)

-- §2.5. Transpose the two legs, dispatch on the tag, and transpose
-- back. The resulting relation can produce *both* tags on one input.
module Sum (A B : Set) where
  module S = Over Rel A B
  projections : S.Span
  projections = S.span (A ⊎ B) (graph inl ˘) (graph inr ˘)
  terminal : S.U.Terminal projections
  S.U.Terminal.enter terminal (S.span X f g) = S.via (copair (f ˘) (g ˘) ˘)
    ((λ { (_ , (refl , p)) → p }) , (λ p → _ , (refl , p)))
    ((λ { (_ , (refl , p)) → p }) , (λ p → _ , (refl , p)))
  -- Observing an output through the matching projection is enough to
  -- recover it; every possible output carries one of the two tags.
  S.U.Terminal.unique terminal {S.span X f g} (S.via h (lf , lb) (rf , rb)) =
    (λ { {b = inl a} p → lf (_ , (refl , p)); {b = inr b} p → rf (_ , (refl , p)) }) ,
    (λ { {b = inl a} p → restore (lb p); {b = inr b} p → restore (rb p) })
    where restore : ∀ {x tag} → Σ (A ⊎ B) (λ z → (tag ≡ z) × h z x) → h tag x
          restore (_ , (refl , p)) = p
