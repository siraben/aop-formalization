{-# OPTIONS --safe --without-K #-}
module AoP.Chapter06.ContainerConverseFold where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_)
open import AoP.Chapter06.AccessibleFoldPreimage using (module Law)
open import AoP.Chapter06.Inductive using (Acc; acc)

-- Theorem 6.4 for containers. A function f assigns a constructor
-- tree to every value. Each R-layer must describe that same tree.
-- Surjectivity provides the layer; induction follows the known tree,
-- so we need no separate accessibility assumption on values.
module Theorem {A Shape : Set} (Pos : Shape → Set) where
  open Law {A} Shape Pos
  module At (R : A ← Layer A) (f : A → Tree)
    (commute : ∀ {a s xs} → R a (s , xs) → f a ≡ branch s (λ i → f (xs i))) where
    open Algebra R using (Fold; node; Child; at)
    -- The book obtains inductivity by pulling constructor membership
    -- back along f. In a container the position is visible: an edge
    -- contains i, and the commuting equation identifies f(child) with
    -- the i-th immediate subtree of f(parent).
    data Subtree : Tree → Tree → Set where
      child : ∀ {s ts} (i : Pos s) → Subtree (ts i) (branch s ts)
    decrease : ∀ {a b} → Child b a → Subtree (f b) (f a)
    decrease (at edge i) rewrite commute edge = child i
    tree-acc : ∀ t → Acc Subtree t
    tree-acc (branch s ts) = acc λ { _ (child i) → tree-acc (ts i) }
    pull : ∀ a → Acc Subtree (f a) → Acc Child a
    pull a (acc smaller) = acc λ b edge → pull b (smaller _ (decrease edge))
    accessible : ∀ a → Acc Child a
    accessible a = pull a (tree-acc (f a))
    -- Local constructor congruence suffices to assemble the child
    -- equalities. For arbitrary function-valued child vectors this is
    -- a real hypothesis when the tree is compared by Agda equality.
    sound : (∀ {s} {u v : Pos s → Tree} → (∀ i → u i ≡ v i) → branch s u ≡ branch s v) →
      ∀ {a t} → Fold a t → f a ≡ t
    sound ext (node edge kids) = commute edge ∙ ext (λ i → sound ext (kids i))

    module Surjective (split : ∀ a → Σ (Layer A) (R a)) where
      complete : ∀ t a → f a ≡ t → Fold a t
      complete (branch s ts) a eq with split a
      ... | (s′ , xs) , edge = assemble s′ xs edge (back (commute edge) ∙ eq) (λ i → complete (ts i))
        where
          back : ∀ {x y : Tree} → x ≡ y → y ≡ x
          back refl = refl
          assemble : ∀ k (vs : Pos k → A) → R a (k , vs) → branch k (λ i → f (vs i)) ≡ branch s ts → (∀ i x → f x ≡ ts i → Fold x (ts i)) → Fold a (branch s ts)
          assemble .s vs e refl ih = node e (λ i → ih i (vs i) refl)
