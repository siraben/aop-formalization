{-# OPTIONS --safe --without-K #-}
module AoP.Chapter04.PreorderFibres where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Power using (Λ; ℙ; _≐_)
open import AoP.Chapter04.LeftDivision using (_＼_)
open import AoP.Chapter04.LexicalOrder using (Pre)
open Pre

-- Exercise 4.49. Send each input to its set of possible outputs.
-- Inclusion of fibres is a partial order on predicates with extensional
-- equality. Pulling it back gives precisely R when R is a preorder.
Incl : ∀ {A : Set} → ℙ A → ℙ A → Set
Incl X Y = ∀ a → X a → Y a
antisym : ∀ {A : Set} (X Y : ℙ A) → Incl X Y → Incl Y X → X ≐ Y
antisym X Y xy yx = xy , yx

module Law {A : Set} (R : A ← A) where
  expand : Pre R → R ⊆ R ＼ R
  expand pre r s = step pre s r
  contract : Pre R → R ＼ R ⊆ R
  contract pre {a} h = h (self pre a)

  characterize : (R ⊆ R ＼ R) → (R ＼ R ⊆ R) → Pre R
  self (characterize into out) a = out (λ s → s)
  step (characterize into out) p q = into q p

  compare : Pre R → ∀ x y → R x y → Incl (Λ R x) (Λ R y)
  compare pre x y r a = expand pre r
  recover : Pre R → ∀ x y → Incl (Λ R x) (Λ R y) → R x y
  recover pre x y h = contract pre (λ {a} → h a)

-- Conversely the pullback of *any* preorder is already a preorder.
pullback : ∀ {A B : Set} (S : B ← B) (f : A → B) → Pre S → Pre (λ x y → S (f x) (f y))
self (pullback S f pre) a = self pre (f a)
step (pullback S f pre) s t = step pre s t
