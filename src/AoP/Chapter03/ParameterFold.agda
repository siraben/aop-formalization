{-# OPTIONS --safe --without-K #-}
module AoP.Chapter03.ParameterFold where

open import AoP.Common.Prelude
open import AoP.Chapter02.Categories using (Fun)
open import AoP.Chapter02.Functors using (Functor)
open import AoP.Chapter02.Initial using (module Theory)

-- Exercise 3.41. For arbitrary endofunctors on Fun, a natural way to
-- route a parameter through one layer suffices. Fold into functions
-- waiting for the parameter; evaluation then supplies the result.
module Law (F G : Functor Fun Fun) (P : Set) where
  open Functor F using () renaming (F₀ to L; F₁ to lf)
  open Functor G using () renaming (F₀ to M; F₁ to mg; composition to comp; resp to resp)
  pairmap : ∀ {X Y : Set} → (X → Y) → P × X → P × Y
  pairmap k (p , x) = p , k x
  module Given (I : Theory.Initial F)
    (route : ∀ {X} → P → L X → M (P × X))
    (natural : ∀ {X Y} (k : X → Y) p t → route p (lf k t) ≡ mg (pairmap k) (route p t))
    {B : Set} (h : M B → B) where
    open Theory.Initial I
    eval : P × (P → B) → B
    eval (p , f) = f p
    alg : L (P → B) → P → B
    alg t p = h (mg eval (route p t))
    solve : P × μ → B
    solve (p , x) = ⦅ alg ⦆ x p
    Equation : (P × μ → B) → Set
    Equation f = ∀ p t → f (p , inn t) ≡ h (mg f (route p t))
    slide : ∀ (k : μ → P → B) p t → alg (lf k t) p ≡ h (mg (λ z → k (snd z) (fst z)) (route p t))
    slide k p t = cong (λ z → h (mg eval z)) (natural k p t) ∙ cong h (back (comp eval (pairmap k) (route p t)))
      where back : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
            back refl = refl
    computes : Equation solve
    computes p t = cong (λ f → f p) (computation alg t) ∙ slide ⦅ alg ⦆ p t

    -- Initial.unique requires equality of the function-valued carriers.
    -- Supply extensionality only for this one function space.
    module Uniqueness (ext : ∀ {f g : P → B} → (∀ p → f p ≡ g p) → f ≡ g) where
      only : ∀ f → Equation f → ∀ z → f z ≡ solve z
      only f eq (p , x) = cong (λ g → g p) (unique alg k square x)
        where k = λ x p → f (p , x)
              square : ∀ t → k (inn t) ≡ alg (lf k t)
              square t = ext λ p → eq p t ∙ back (slide k p t)
                where back : ∀ {a b : B} → a ≡ b → b ≡ a
                      back refl = refl
