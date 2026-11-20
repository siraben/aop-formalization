{-# OPTIONS --safe --without-K #-}
module AoP.MonotoneMinimum where

open import AoP.Prelude
open import AoP.Thinning using (Pred; Min)
open import AoP.Polynomial using (_⊎_; inl; inr)

-- §7.2, Theorem 7.1 for unary functions. When can a program minimize
-- *before* applying f instead of searching its entire image? Precisely
-- when f preserves the order. A two-element test set suffices to recover
-- monotonicity from the putative optimization rule. Min includes a
-- membership witness, so nothing here presumes a minimum of the empty set.
module Law {A B : Set} (_≤₁_ : A → A → Set) (_≤₂_ : B → B → Set)
           (rid : ∀ a → a ≤₁ a) (f : A → B) where
  Image : Pred A → Pred B
  Image X b = Σ A λ a → X a × (f a ≡ b)

  Monotone = ∀ {a b} → a ≤₁ b → f a ≤₂ f b
  Distributes = ∀ X m → Min _≤₁_ m X → Min _≤₂_ (f m) (Image X)

  distribute : Monotone → Distributes
  distribute mono X m (member , least) = (m , member , refl) , λ where
    _ (a , x , refl) → mono (least a x)

  monotone : Distributes → Monotone
  monotone dist {a} {b} ab = snd (dist pair a (inl refl , least)) (f b) (b , inr refl , refl)
    where
    pair : Pred A
    pair x = (a ≡ x) ⊎ (b ≡ x)

    least : ∀ x → pair x → a ≤₁ x
    least _ (inl refl) = rid a
    least _ (inr refl) = ab
