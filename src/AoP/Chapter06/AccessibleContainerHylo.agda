{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.AccessibleContainerHylo where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _⊆_)
open import AoP.Chapter06.Inductive using (Acc; acc)
open import AoP.Chapter06.ContainerHyloSimple using (module Law)

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

    -- Second clause of Theorem 6.3: a total producer supplies a layer
    -- and a total consumer accepts the resulting vector of answers.
    -- The recursive result at position i contains both the answer and
    -- its derivation, so projecting these needs no choice axiom.
    module Entire (emit : ∀ x → Σ (Layer A) (λ l → produce l x))
      (reduce : ∀ l → Σ B (λ y → consume y l)) where
      run : ∀ x → Acc Child x → Σ B (λ y → Tree y x)
      run x (acc smaller) with emit x
      ... | (s , xs) , p = assemble (λ i → run (xs i) (smaller _ (at p i)))
        where
          assemble : (kids : ∀ i → Σ B (λ y → Tree y (xs i))) → Σ B (λ y → Tree y x)
          assemble kids with reduce (s , λ i → fst (kids i))
          ... | y , c = y , done p (λ i → snd (kids i)) c

      -- Corollary 6.2. If each layer and output are determined, this
      -- executable answer represents the whole least relation. The
      -- consumer respects pointwise equality of its child vector.
      module Function (wf : ∀ x → Acc Child x)
        (layer-unique : ∀ {x l m} → produce l x → produce m x → l ≡ m)
        (result-unique : ∀ {s} {f g : Pos s → B} {y z} → (∀ i → f i ≡ g i) → consume y (s , f) → consume z (s , g) → y ≡ z) where
        eval : A → B
        eval x = fst (run x (wf x))
        single : ∀ {x y z} → Tree y x → Tree z x → y ≡ z
        single (done p kids c) (done q others d) with layer-unique p q
        ... | refl = result-unique (λ i → single (kids i) (others i)) c d
        graph-in : ∀ x → Tree (eval x) x
        graph-in x = snd (run x (wf x))
        graph-out : ∀ {x y} → Tree y x → y ≡ eval x
        graph-out h = single h (graph-in _)
