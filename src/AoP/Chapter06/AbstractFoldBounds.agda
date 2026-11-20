{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.AbstractFoldBounds where

open import AoP.Chapter02.Categories
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter04.ProductAllegory using (Laws)

-- §6.2 (6.4–5). Move a comparison through one unfolded layer.
-- Both fusion directions test the *same* candidate, s after r.
module Proof {o h e p} {C : Category o h e} (L : Laws C p) (F : Functor C C) where
  open Category C
  open Laws L
  private module F = Functor F
  module At {I A B} (out : Hom I (F.F₀ I)) (R : Hom (F.F₀ A) A) (T : Hom (F.F₀ B) B)
    (r : Hom I A) (t : Hom I B) (s : Hom A B) where
    step : ∀ {X} → Hom (F.F₀ X) X → Hom I X → Hom I X
    step alg x = (alg ∘ F.F₁ x) ∘ out
    -- Both local inclusions can be placed in this context by
    -- monotonicity: keep the recursive child and the constructor fixed.
    ctx : Hom (F.F₀ A) B → Hom I B
    ctx k = (k ∘ F.F₁ r) ∘ out
    expose : step T (s ∘ r) ≈ ctx (T ∘ F.F₁ s)
    expose = compose-cong (transitive (compose-cong reflexive (F.composition s r))
                              (symmetric (assoc _ _ _))) reflexive
    collect : ctx (s ∘ R) ≈ (s ∘ step R r)
    collect = transitive (compose-cong (assoc _ _ _) reflexive) (assoc _ _ _)
    lift-bound : ∀ {k l} → k ⊑ l → ctx k ⊑ ctx l
    lift-bound sub = mono (mono sub (respect reflexive)) (respect reflexive)
    upper : step R r ⊑ r → (∀ x → step T x ⊑ x → t ⊑ x) → (T ∘ F.F₁ s) ⊑ (s ∘ R) → t ⊑ (s ∘ r)
    upper roll least sub = least _ (trans (respect expose) (trans (lift-bound sub)
      (trans (respect collect) (mono (respect reflexive) roll))))
    lower : r ⊑ step R r → (∀ x → x ⊑ step T x → x ⊑ t) → (s ∘ R) ⊑ (T ∘ F.F₁ s) → (s ∘ r) ⊑ t
    lower unroll greatest sub = greatest _ (trans (mono (respect reflexive) unroll)
      (trans (respect (symmetric collect)) (trans (lift-bound sub) (respect (symmetric expose)))))
