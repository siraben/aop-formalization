{-# OPTIONS --safe --without-K #-}
module AoP.Chapter09.DPContextCost where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations using (_←_; _⊆_; _∘_; _˘; _⊓_)

-- Proposition 9.3: attach an input to a cost. Two feasible results
-- may be compared in context only if they have a common input. An
-- individual result determines at most one input (simplicity of H˘).
module Law {A C I : Set} (F : Set → Set) (L : ∀ {X Y} → Y ← X → F Y ← F X)
  (mono : ∀ {X Y} (P Q : Y ← X) → P ⊆ Q → L P ⊆ L Q)
  (join : ∀ {X Y Z} (P : Z ← Y) (Q : Y ← X) → L P ∘ L Q ⊆ L (P ∘ Q))
  (split : ∀ {X Y Z} (P : Z ← Y) (Q : Y ← X) → L (P ∘ Q) ⊆ L P ∘ L Q)
  (cost : A → C) (H : A ← I) (simple : ∀ {x i j} → H x i → H x j → i ≡ j)
  (le : C ← C) (h : F A → A) (k : F (C × I) → C) where
  Pair : (C × I) ← A
  Pair (c , i) x = (cost x ≡ c) × H x i
  SameInput : (C × I) ← (C × I)
  SameInput (c , i) (e , j) = le c e × (i ≡ j)
  R : A ← A
  R x y = le (cost x) (cost y)
  Guard = R ⊓ (H ∘ H ˘)
  transfer : Pair ∘ Guard ⊆ SameInput ∘ Pair
  transfer (_ , (refl , hx) , better , i , hx′ , hy) = (_ , i) , (better , simple hx hx′) , refl , hy

  -- Both directions of graph (cost ∘ h) = graph k ∘ L Pair:
  -- a paired layer exists, and every such layer computes that cost.
  private
    sym : ∀ {c d : C} → c ≡ d → d ≡ c
    sym refl = refl
  module Factor (enter : ∀ x → Σ _ λ u → L Pair u x × (k u ≡ cost (h x)))
    (exit : ∀ {u x} → L Pair u x → k u ≡ cost (h x))
    (ordered : ∀ {u v} → L SameInput u v → le (k u) (k v)) where
    monotone : ∀ {x y} → L Guard x y → R (h x) (h y)
    monotone {x} {y} g with enter x
    ... | u , p , eq with split SameInput Pair (mono (Pair ∘ Guard) (SameInput ∘ Pair) transfer (join Pair Guard (x , p , g)))
    ... | v , cmp , q rewrite sym eq | sym (exit q) = ordered cmp
