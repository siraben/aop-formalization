{-# OPTIONS --safe --without-K #-}
module AoP.FibreGenerationTransport where

open import AoP.Prelude
open import AoP.Relations using (_←_; _⊆_; _∘_)
open import AoP.Shunting using (graph)

-- 8.11. A layer of children carrying certificates projects to a layer
-- of inputs. Evaluating X there is equivalent to evaluating X ∘ val
-- on the original layer. In particular the reverse direction recovers
-- a lifted relation over certified children, ready for fibre simulation.
module Law {A C B : Set} (F : Set → Set) (L : ∀ {X Y} → Y ← X → F Y ← F X)
  (val : C → A) (project : F C → F A)
  (intro : graph project ⊆ L (graph val)) (elim : L (graph val) ⊆ graph project)
  (join : ∀ {X Y Z} (P : Z ← Y) (Q : Y ← X) → L P ∘ L Q ⊆ L (P ∘ Q))
  (split : ∀ {X Y Z} (P : Z ← Y) (Q : Y ← X) → L (P ∘ Q) ⊆ L P ∘ L Q) where
  enter : ∀ (X : B ← A) {t b} → L X b (project t) → L (X ∘ graph val) b t
  enter X p = join X (graph val) (_ , p , intro refl)
  exit : ∀ (X : B ← A) {t b} → L (X ∘ graph val) b t → L X b (project t)
  exit X p with split X (graph val) p
  ... | a , x , g with elim g
  ... | refl = x
