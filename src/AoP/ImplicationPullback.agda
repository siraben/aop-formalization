{-# OPTIONS --safe --without-K #-}
module AoP.ImplicationPullback where

open import AoP.Prelude
open import AoP.Relations
open import AoP.RelImplication using (_⇒_)
open import AoP.Shunting using (graph)

-- Exercise 4.33. Reindex both endpoints of an implication by functions.
-- In graph notation the composite contains two existential witnesses;
-- graph equalities force them to be exactly the reindexed endpoints.
module Law {A B C D : Set} (f : C → B) (g : D → A) where
  pull : (B ← A) → C ← D
  pull R = graph f ˘ ∘ R ∘ graph g

  read-edge : (R : B ← A) → ∀ {c d} → pull R c d → R (f c) (g d)
  read-edge R (_ , refl , _ , r , refl) = r

  write-edge : (R : B ← A) → ∀ {c d} → R (f c) (g d) → pull R c d
  write-edge R {c} {d} r = f c , refl , g d , r , refl

  distribute : (R S : B ← A) → pull (R ⇒ S) ⊆ pull R ⇒ pull S
  distribute R S {c} {d} h r = write-edge S (read-edge (R ⇒ S) h (read-edge R r))

  collect : (R S : B ← A) → (pull R ⇒ pull S) ⊆ pull (R ⇒ S)
  collect R S {c} {d} h = write-edge (R ⇒ S) (λ r → read-edge S (h (write-edge R r)))
