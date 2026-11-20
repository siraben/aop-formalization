{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.InjectionTests where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Shunting using (Id; graph)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter04.Complement using (⊥; _⊔_)
open import AoP.Chapter05.CopairCancellation using (copair)

-- Exercise 5.12 in Rel. Reading the left column of a tagged input
-- succeeds only on a left tag; reading the right column is symmetric.
module Cases (A B : Set) where
  empty : ∀ {U V : Set} → U ← V
  empty _ _ = ⊥
  X : A ← (A ⊎ B)
  X = copair Id empty
  Y : B ← (A ⊎ B)
  Y = copair empty Id
  L : (A ⊎ B) ← A
  L = graph inl
  R : (A ⊎ B) ← B
  R = graph inr

  left-ok : X ∘ L ⊆ Id
  left-ok (_ , p , refl) = p
  left-ok′ : Id ⊆ X ∘ L
  left-ok′ refl = _ , refl , refl
  right-ok : Y ∘ R ⊆ Id
  right-ok (_ , p , refl) = p
  right-ok′ : Id ⊆ Y ∘ R
  right-ok′ refl = _ , refl , refl
  cross-l : X ∘ R ⊆ empty
  cross-l (_ , p , refl) = p
  cross-r : Y ∘ L ⊆ empty
  cross-r (_ , p , refl) = p

  partition : (L ∘ X) ⊔ (R ∘ Y) ⊆ Id
  partition {a = inl a} (inl (_ , refl , refl)) = refl
  partition {a = inr b} (inr (_ , refl , refl)) = refl
  restore : Id ⊆ (L ∘ X) ⊔ (R ∘ Y)
  restore {inl _} refl = inl (_ , refl , refl)
  restore {inr _} refl = inr (_ , refl , refl)

  left-inverse : X ⊆ L ˘
  left-inverse {a = inl _} refl = refl
  right-inverse : Y ⊆ R ˘
  right-inverse {a = inr _} refl = refl
  left-read : L ˘ ⊆ X
  left-read refl = refl
  right-read : R ˘ ⊆ Y
  right-read refl = refl

  module Formula {C : Set} (P : C ← A) (Q : C ← B) where
    split : copair P Q ⊆ (P ∘ L ˘) ⊔ (Q ∘ R ˘)
    split {a = inl a} p = inl (a , p , refl)
    split {a = inr b} q = inr (b , q , refl)
    merge : (P ∘ L ˘) ⊔ (Q ∘ R ˘) ⊆ copair P Q
    merge (inl (_ , p , refl)) = p
    merge (inr (_ , q , refl)) = q
