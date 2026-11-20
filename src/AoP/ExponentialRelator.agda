{-# OPTIONS --safe --without-K #-}
module AoP.ExponentialRelator where

open import AoP.Prelude
open import AoP.Relations
open import AoP.Shunting using (Id; graph)

-- Exercise 5.3. Fix a set of indices X. Relate two X-indexed families
-- when their entries are related at every index. A composite supplies
-- an intermediate entry at each x; collecting these entries gives the
-- intermediate family. Use pointwise equality on families throughout.
module Lift (X : Set) where
  lift : ∀ {A B} → B ← A → (X → B) ← (X → A)
  lift R g f = ∀ x → R (g x) (f x)

  mono : ∀ {A B} (R S : B ← A) → R ⊆ S → lift R ⊆ lift S
  mono R S incl all x = incl (all x)

  module Composite {A B C : Set} (S : C ← B) (R : B ← A) where
    collect : lift (S ∘ R) ⊆ lift S ∘ lift R
    collect all = (λ x → fst (all x)) , (λ x → fst (snd (all x))) , (λ x → snd (snd (all x)))
    split : lift S ∘ lift R ⊆ lift (S ∘ R)
    split (g , s , r) x = g x , s x , r x

  identity : ∀ {A} (f g : X → A) → lift Id g f ≡ (∀ x → g x ≡ f x)
  identity f g = refl
  action : ∀ {A B} (h : A → B) (g : X → B) (f : X → A) →
           lift (graph h) g f ≡ (∀ x → h (f x) ≡ g x)
  action h g f = refl
  converse : ∀ {A B} (R : B ← A) (f : X → A) (g : X → B) → lift (R ˘) f g ≡ lift R g f
  converse R f g = refl
