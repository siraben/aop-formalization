{-# OPTIONS --safe --without-K #-}
module AoP.AccumulatorFusion where

open import AoP.Prelude
open import AoP.Categories using (Fun)
open import AoP.Functors using (Functor)
open import AoP.Initial using (module Theory)

-- Exercise 3.45. Replace a fold that returns an answer by one that
-- returns a function of a pending accumulator. The fusion square says
-- how to carry the pending work through one constructor. At the end,
-- supplying a neutral accumulator recovers the original answer.
module Derive (F : Functor Fun Fun) (I : Theory.Initial F) where
  open Theory F using (Algebra; Hom)
  open Theory.Initial I
  open Theory.Laws F I using (fusion)

  recover : ∀ {A E : Set} (f : Algebra A) (g : Algebra (E → A))
            (k : A → E → A) (e : E) → (∀ a → k a e ≡ a) → Hom f g k →
            ∀ x → ⦅ f ⦆ x ≡ ⦅ g ⦆ x e
  recover f g k e neutral square x = begin
    ⦅ f ⦆ x       ≡⟨ back (neutral (⦅ f ⦆ x)) ⟩
    k (⦅ f ⦆ x) e ≡⟨ cong (λ pending → pending e) (fusion f g k square x) ⟩
    ⦅ g ⦆ x e ∎
    where back : ∀ {X : Set} {a b : X} → a ≡ b → b ≡ a
          back refl = refl
