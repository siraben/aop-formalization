{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.Closure where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Shunting using (Id)
open import AoP.Chapter04.Complement using (_⊔_)
open import AoP.Chapter02.Polynomial using (inl; inr)

-- §6.7. A witness is a finite path, stored with its final edge outside.
module Paths {A : Set} (R : A ← A) where
  data Star : A ← A where
    stop : ∀ {a} → Star a a
    extend : ∀ {a b c} → R c b → Star b a → Star c a

  singleton : R ⊆ Star
  singleton r = extend r stop

  append : Star ∘ Star ⊆ Star
  append (_ , stop , p) = p
  append (_ , extend r q , p) = extend r (append (_ , q , p))

  -- The least prefixpoint of X ↦ Id ∪ R ∘ X (equation 6.8).
  close : Id ⊔ (R ∘ Star) ⊆ Star
  close (inl refl) = stop
  close (inr (_ , r , p)) = extend r p

  expose : Star ⊆ Id ⊔ (R ∘ Star)
  expose stop = inl refl
  expose (extend r p) = inr (_ , r , p)

  induction : (X : A ← A) → Id ⊔ (R ∘ X) ⊆ X → Star ⊆ X
  induction X step stop = step (inl refl)
  induction X step (extend r p) = step (inr (_ , r , induction X step p))

  -- Universal property: a reflexive, transitive extension already
  -- contains the whole closure. Conversely it must contain single edges.
  least-preorder : (X : A ← A) → Id ⊆ X → X ∘ X ⊆ X → R ⊆ X → Star ⊆ X
  least-preorder X unit trans sub = induction X λ where
    (inl eq) → unit eq
    (inr (b , r , x)) → trans (b , sub r , x)

  restrict : (X : A ← A) → Star ⊆ X → R ⊆ X
  restrict X sub r = sub (singleton r)
