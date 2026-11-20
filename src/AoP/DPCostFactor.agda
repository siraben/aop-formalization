{-# OPTIONS --safe --without-K #-}
module AoP.DPCostFactor where

open import AoP.Prelude
open import AoP.Relations using (_←_; _⊆_; _∘_)
open import AoP.Shunting using (graph)

-- Proposition 9.2. Compare solutions through their costs. To establish
-- monotonicity of an evaluator h, move the comparison down to the
-- cost algebra k, using the factorization cost (h x) = k (f x).
module Law {A C : Set} (F : Set → Set) (L : ∀ {X Y} → Y ← X → F Y ← F X)
  (mono : ∀ {X Y} (P Q : Y ← X) → P ⊆ Q → L P ⊆ L Q)
  (join : ∀ {X Y Z} (P : Z ← Y) (Q : Y ← X) → L P ∘ L Q ⊆ L (P ∘ Q))
  (split : ∀ {X Y Z} (P : Z ← Y) (Q : Y ← X) → L (P ∘ Q) ⊆ L P ∘ L Q)
  (cost : A → C) (f : F A → F C)
  (intro : graph f ⊆ L (graph cost)) (elim : L (graph cost) ⊆ graph f)
  (le : C ← C) (h : F A → A) (k : F C → C)
  (factor : ∀ x → cost (h x) ≡ k (f x))
  (ordered : ∀ {x y} → L le x y → le (k x) (k y)) where
  R : A ← A
  R x y = le (cost x) (cost y)
  move-cost : graph cost ∘ R ⊆ le ∘ graph cost
  move-cost (_ , refl , r) = _ , r , refl
  move-layer : ∀ {x y} → L R x y → L le (f x) (f y)
  move-layer {x} r with split le (graph cost) (mono (graph cost ∘ R) (le ∘ graph cost) move-cost
                                  (join (graph cost) R (x , intro refl , r)))
  ... | m , le′ , g with elim g
  ... | refl = le′
  monotone : ∀ {x y} → L R x y → R (h x) (h y)
  monotone {x} {y} r rewrite factor x | factor y = ordered (move-layer r)
