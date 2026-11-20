{-# OPTIONS --safe --without-K #-}
module AoP.DiscreteDiagramClosure where

open import AoP.Prelude

-- Exercise 3.37, positive case: diagrams of sets on a discrete index
-- set have no nonidentity naturality squares. A map is exactly a family
-- of component maps. Verify the exponential by its evaluation equation
-- and uniqueness, comparing maps pointwise in both arguments.
module Families (I : Set) where
  Obj = I → Set
  Map : Obj → Obj → Set
  Map A B = ∀ i → A i → B i
  Product Exp : Obj → Obj → Obj
  Product A B i = A i × B i
  Exp A B i = A i → B i
  One : Obj
  One i = ⊤
  terminate : ∀ {A} → Map A One
  terminate i a = tt
  terminal-unique : ∀ {A} (g : Map A One) i a → g i a ≡ tt
  terminal-unique g i a = refl
  pair : ∀ {A B C} → Map C A → Map C B → Map C (Product A B)
  pair f g i c = f i c , g i c
  project₁ : ∀ {A B} → Map (Product A B) A
  project₁ i = fst
  project₂ : ∀ {A B} → Map (Product A B) B
  project₂ i = snd
  pair₁ : ∀ {A B C} (f : Map C A) (g : Map C B) i c → project₁ {A} {B} i (pair {A} {B} {C} f g i c) ≡ f i c
  pair₁ f g i c = refl
  pair₂ : ∀ {A B C} (f : Map C A) (g : Map C B) i c → project₂ {A} {B} i (pair {A} {B} {C} f g i c) ≡ g i c
  pair₂ f g i c = refl
  pair-unique : ∀ {A B C} (h : Map C (Product A B)) (f : Map C A) (g : Map C B) →
    (∀ i c → fst (h i c) ≡ f i c) → (∀ i c → snd (h i c) ≡ g i c) →
    ∀ i c → h i c ≡ pair {A} {B} {C} f g i c
  pair-unique h f g first second i c = cong (_, snd (h i c)) (first i c) ∙ cong (f i c ,_) (second i c)
  eval : ∀ {A B} → Map (Product (Exp A B) A) B
  eval i (f , a) = f a
  curry : ∀ {A B C} → Map (Product C A) B → Map C (Exp A B)
  curry f i c a = f i (c , a)
  apply : ∀ {A B C} → Map C (Exp A B) → Map (Product C A) B
  apply {A} {B} g i (c , a) = eval {A} {B} i (g i c , a)
  beta : ∀ {A B C} (f : Map (Product C A) B) i p → apply {A} {B} {C} (curry {A} {B} {C} f) i p ≡ f i p
  beta f i (c , a) = refl
  unique : ∀ {A B C} (g : Map C (Exp A B)) (f : Map (Product C A) B) →
    (∀ i p → apply {A} {B} {C} g i p ≡ f i p) → ∀ i c a → g i c a ≡ curry {A} {B} {C} f i c a
  unique g f equation i c a = equation i (c , a)
