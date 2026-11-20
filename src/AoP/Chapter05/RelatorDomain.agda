{-# OPTIONS --safe --without-K #-}
module AoP.Chapter05.RelatorDomain where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter04.Shunting using (Id)
open import AoP.Chapter04.DomainPullback using (dom)

-- Exercise 5.5. The domain is a test. Two more facts characterize it:
-- each accepted input has a successor, and every edge starts at an
-- accepted input. Transport these facts through the relator separately;
-- this avoids assuming that arbitrary intersections are preserved.
module Law (F : Set → Set) (lift : ∀ {A B} → (B ← A) → F B ← F A)
           (mono : ∀ {A B} (R S : B ← A) → R ⊆ S → lift R ⊆ lift S)
           (identity : ∀ {A} → lift (Id {A}) ⊆ Id)
           (split : ∀ {A B C} (S : C ← B) (R : B ← A) → lift (S ∘ R) ⊆ lift S ∘ lift R) where
  module At {A B : Set} (R : B ← A) where
    private
      test : dom R ⊆ Id
      test = fst
      returns : dom R ⊆ R ˘ ∘ R
      returns (refl , b , r) = b , r , r
      restrict : R ⊆ R ∘ dom R
      restrict {b} {a} r = a , r , refl , b , r

      lifted-test : lift (dom R) ⊆ Id
      lifted-test p = identity (mono (dom R) Id test p)

    forward : lift (dom R) ⊆ dom (lift R)
    forward p with split (R ˘) R (mono (dom R) (R ˘ ∘ R) returns p)
    ... | y , _ , r with lifted-test p
    ... | refl = refl , y , r

    backward : dom (lift R) ⊆ lift (dom R)
    backward (refl , y , r) with split R (dom R) (mono R (R ∘ dom R) restrict r)
    ... | x , _ , p with lifted-test p
    ... | refl = p
