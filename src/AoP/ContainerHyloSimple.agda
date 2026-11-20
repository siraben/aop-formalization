{-# OPTIONS --safe --without-K #-}
module AoP.ContainerHyloSimple where

open import AoP.Prelude
open import AoP.Relations using (_←_)

-- Exercise 6.10. A finite derivation chooses a producer layer and
-- solves every recursive position before applying the consumer.
-- Neither relation must return a result on every input. Uniqueness
-- compares only completed derivations, descending on the first one.
module Law {A B : Set} (Shape : Set) (Pos : Shape → Set) where
  Layer : Set → Set
  Layer X = Σ Shape λ s → Pos s → X
  module Run (produce : Layer A ← A) (consume : B ← Layer B)
    (one-layer : ∀ {x l m} → produce l x → produce m x → l ≡ m)
    (one-output : ∀ {s} {f g : Pos s → B} {u v} → (∀ i → f i ≡ g i) →
                  consume u (s , f) → consume v (s , g) → u ≡ v) where
    data Hylo : B ← A where
      node : ∀ {s} {xs : Pos s → A} {ys : Pos s → B} {x y} → produce (s , xs) x →
             (∀ i → Hylo (ys i) (xs i)) → consume y (s , ys) → Hylo y x

    -- Factor successful runs through their intermediate constructor tree.
    -- These functions also justify the unfold/fold composite reading
    -- of the fused derivation, without a totality assumption.
    data Tree : Set where
      branch : (s : Shape) → (Pos s → Tree) → Tree
    data Unfold : Tree ← A where
      emit : ∀ {s xs kids x} → produce (s , xs) x → (∀ i → Unfold (kids i) (xs i)) → Unfold (branch s kids) x
    data Fold : B ← Tree where
      reduce : ∀ {s ys kids y} → (∀ i → Fold (ys i) (kids i)) → consume y (s , ys) → Fold y (branch s kids)
    factor : ∀ {x y} → Hylo y x → Σ Tree λ t → Fold y t × Unfold t x
    factor (node {s} p kids c) = branch s (λ i → fst (factor (kids i))) ,
      reduce (λ i → fst (snd (factor (kids i)))) c , emit p (λ i → snd (snd (factor (kids i))))
    fuse : ∀ {t x y} → Fold y t → Unfold t x → Hylo y x
    fuse (reduce fs c) (emit p us) = node p (λ i → fuse (fs i) (us i)) c

    simple : ∀ {x y z} → Hylo y x → Hylo z x → y ≡ z
    simple (node p kids c) (node q others d) with one-layer p q
    ... | refl = one-output (λ i → simple (kids i) (others i)) c d

    composite-simple : ∀ {x y z t u} → Fold y t → Unfold t x → Fold z u → Unfold u x → y ≡ z
    composite-simple f p g q = simple (fuse f p) (fuse g q)
