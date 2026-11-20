{-# OPTIONS --safe --without-K #-}
module AoP.InhabitedFunctor where

open import AoP.Prelude
open import AoP.Complement using (⊥)
open import AoP.Relations using (_←_; _⊆_; _∘_; _˘)
open import AoP.Shunting using (graph)
open import AoP.Polynomial using (_⊎_; inl; inr)
open import Agda.Builtin.Bool using (Bool; false; true)

-- Exercise 5.4. Supply the empty/inhabited classification per object,
-- avoiding a global decision of inhabitation for arbitrary Agda types.
record Object : Set₁ where
  constructor obj
  field carrier : Set
        classify : carrier ⊎ (carrier → ⊥)
open Object
Small : Object → Set
Small (obj A (inl _)) = ⊤
Small (obj A (inr _)) = ⊥
absurd : ∀ {A : Set} → ⊥ → A
absurd ()
map : ∀ X Y → (carrier X → carrier Y) → Small X → Small Y
map (obj _ (inr _)) Y f ()
map (obj _ (inl _)) (obj _ (inl _)) f _ = tt
map (obj _ (inl x)) (obj _ (inr no)) f _ = absurd (no (f x))
unique : ∀ X (x y : Small X) → x ≡ y
unique (obj _ (inl _)) tt tt = refl
unique (obj _ (inr _)) ()
identity : ∀ X x → map X X (λ a → a) x ≡ x
identity X x = unique X _ _
composition : ∀ X Y Z (g : carrier Y → carrier Z) (f : carrier X → carrier Y) x →
              map X Z (λ a → g (f a)) x ≡ map Y Z g (map X Y f x)
composition X Y Z g f x = unique Z _ _

-- Only three classified objects are needed for the obstruction. Two
-- distinct constants have disjoint images. Their overlap factors via
-- the empty object, whose image is still empty. Yet their images as
-- functions are both the sole map between singletons.
O = obj ⊥ (inr (λ x → x))
I = obj ⊤ (inl tt)
B = obj Bool (inl false)
f g : ⊤ → Bool
f _ = false
g _ = true
e : ⊥ → ⊤
e ()
module Obstruction
  (F : ∀ X Y → carrier Y ← carrier X → Small Y ← Small X)
  (mono : ∀ X Y (R S : carrier Y ← carrier X) → R ⊆ S → F X Y R ⊆ F X Y S)
  (fun : ∀ X Y (h : carrier X → carrier Y) → graph (map X Y h) ⊆ F X Y (graph h))
  (conv : ∀ X Y (R : carrier Y ← carrier X) → (F X Y R) ˘ ⊆ F Y X (R ˘))
  (compose : ∀ X Y Z (S : carrier Z ← carrier Y) (R : carrier Y ← carrier X) →
     F Y Z S ∘ F X Y R ⊆ F X Z (S ∘ R))
  (decompose : ∀ X Y Z (S : carrier Z ← carrier Y) (R : carrier Y ← carrier X) →
     F X Z (S ∘ R) ⊆ F Y Z S ∘ F X Y R) where
  private
    common = graph f ˘ ∘ graph g
    via-empty = graph e ∘ graph e ˘
    disjoint : common ⊆ via-empty
    disjoint (.false , refl , ())
    hit : F I I common tt tt
    hit = compose I B I (graph f ˘) (graph g) (tt , conv I B (graph f) (fun I B f refl) , fun I B g refl)
  impossible : ⊥
  impossible = fst (decompose I O I (graph e) (graph e ˘) (mono I I common via-empty disjoint hit))
