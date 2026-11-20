{-# OPTIONS --safe --without-K #-}
module AoP.AccessibleContainerHylo where

open import AoP.Prelude
open import AoP.Relations using (_←_; _⊆_)
open import AoP.Inductive using (Acc; acc)
open import AoP.ContainerHyloSimple using (module Law)

-- Theorem 6.3 for shape-and-position layers. A predecessor is any
-- input requested at any position of any allowed producer layer.
module Solve {A B : Set} (Shape : Set) (Pos : Shape → Set) where
  open Law {A} {B} Shape Pos using (Layer)
  module Run (produce : Layer A ← A) (consume : B ← Layer B) where
    data Child : A ← A where
      at : ∀ {x s xs} → produce (s , xs) x → (i : Pos s) → Child (xs i) x
    data Step (X : B ← A) : B ← A where
      node : ∀ {x y s xs ys} → produce (s , xs) x → (∀ i → X (ys i) (xs i)) → consume y (s , ys) → Step X y x
    data Tree : B ← A where
      done : ∀ {x y s xs ys} → produce (s , xs) x → (∀ i → Tree (ys i) (xs i)) → consume y (s , ys) → Tree y x
    roll : Step Tree ⊆ Tree
    roll (node p kids c) = done p kids c
    unroll : Tree ⊆ Step Tree
    unroll (done p kids c) = node p kids c
    least : ∀ X → Step X ⊆ X → Tree ⊆ X
    least X closed (done p kids c) = closed (node p (λ i → least X closed (kids i)) c)
    -- Unfold a rival solution once. Its choice of layer determines
    -- exactly which smaller inputs the accessibility proof must cover.
    greatest : ∀ X → X ⊆ Step X → ∀ {x y} → Acc Child x → X y x → Tree y x
    greatest X open-step (acc smaller) edge with open-step edge
    ... | node p kids c = done p (λ i → greatest X open-step (smaller _ (at p i)) (kids i)) c
    unique : (∀ x → Acc Child x) → ∀ X → Step X ⊆ X → X ⊆ Step X → (Tree ⊆ X) × (X ⊆ Tree)
    unique wf X closed expand = least X closed , λ { {b} {a} h → greatest X expand (wf a) h }
