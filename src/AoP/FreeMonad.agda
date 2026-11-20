{-# OPTIONS --safe --without-K #-}
module AoP.FreeMonad where

open import AoP.Prelude
open import AoP.Categories using (Fun)
open import AoP.Functors using (Functor)
open import AoP.Initial using (module Theory)
open import AoP.FreeSubstitution using (module Free)
open import AoP.Polynomial using (inl; inr)

-- Exercise 2.40. Renaming substitutes a variable leaf at each leaf;
-- flattening substitutes each leaf's term directly. The substitution
-- laws give the functor, naturality, and monad equations for every G
-- for which the required family of initial term algebras exists in Fun.
module Monad (G : Functor Fun Fun) (I : ∀ A → Theory.Initial (Free.Layer G A)) where
  open Free.Terms G I
  back : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  back refl = refl

  congruent : ∀ {A B} (k j : A → Term B) → (∀ a → k a ≡ j a) → ∀ t → sub k t ≡ sub j t
  congruent {A} k j eq = T.unique A (alg j) (sub k) λ where
    (inl a) → variable-law k a ∙ eq a
    (inr t) → op-law k t

  rename : ∀ {A B} → (A → B) → Term A → Term B
  rename f = sub (λ a → var (f a))

  terms : Functor Fun Fun
  Functor.F₀ terms = Term
  Functor.F₁ terms = rename
  Functor.resp terms eq = congruent _ _ (λ x → cong var (eq x))
  Functor.identity terms = unchanged
  Functor.composition terms g f t = back (compose _ _ t ∙ congruent _ _ (λ a → variable-law (λ b → var (g b)) (f a)) t)

  join : ∀ {A} → Term (Term A) → Term A
  join = sub (λ t → t)

  var-natural : ∀ {A B} (f : A → B) a → rename f (var a) ≡ var (f a)
  var-natural f = variable-law _

  join-natural : ∀ {A B} (f : A → B) t → rename f (join t) ≡ join (rename (rename f) t)
  join-natural f t = compose (λ x → x) _ t ∙ back (compose _ (λ x → x) t ∙ congruent _ _ (λ a → variable-law (λ x → x) (rename f a)) t)

  outer-unit : ∀ {A} (t : Term A) → join (var t) ≡ t
  outer-unit = variable-law _
  inner-unit : ∀ {A} (t : Term A) → join (rename var t) ≡ t
  inner-unit t = compose _ (λ x → x) t ∙ congruent _ var (λ a → variable-law (λ x → x) (var a)) t ∙ unchanged t

  associate : ∀ {A} (t : Term (Term (Term A))) → join (join t) ≡ join (rename join t)
  associate t = compose (λ x → x) (λ x → x) t ∙ back (compose _ (λ x → x) t ∙ congruent _ _ (λ a → variable-law (λ x → x) (join a)) t)
