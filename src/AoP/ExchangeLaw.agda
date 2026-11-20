{-# OPTIONS --safe --without-K #-}
module AoP.ExchangeLaw where

open import AoP.Categories

-- Exercise 2.27. Given four arrows arranged as two inputs by two
-- outputs, either choose the input before pairing its outputs, or pair
-- the two case analyses. Observe the result through each projection;
-- in each case it suffices to check the two injections.
module Exchange {o h e} (C : Category o h e) where
  open Category C
  module Diagram {A B D E S P : Obj}
    (i : Hom A S) (j : Hom B S) (l : Hom P D) (r : Hom P E)
    (pair : ∀ {X} → Hom X D → Hom X E → Hom X P)
    (left : ∀ {X} (f : Hom X D) g → l ∘ pair f g ≈ f)
    (right : ∀ {X} f (g : Hom X E) → r ∘ pair f g ≈ g)
    (pair-ext : ∀ {X} (a b : Hom X P) → l ∘ a ≈ l ∘ b → r ∘ a ≈ r ∘ b → a ≈ b)
    (cases : ∀ {X} → Hom A X → Hom B X → Hom S X)
    (inl : ∀ {X} (f : Hom A X) g → cases f g ∘ i ≈ f)
    (inr : ∀ {X} f (g : Hom B X) → cases f g ∘ j ≈ g)
    (case-ext : ∀ {X} (a b : Hom S X) → a ∘ i ≈ b ∘ i → a ∘ j ≈ b ∘ j → a ≈ b) where

    project : ∀ {X} (p : Hom P X) (a : Hom A P) (b : Hom B P) →
              p ∘ cases a b ≈ cases (p ∘ a) (p ∘ b)
    project p a b = case-ext _ _
      (transitive (assoc _ _ _) (transitive (compose-cong reflexive (inl a b)) (symmetric (inl _ _))))
      (transitive (assoc _ _ _) (transitive (compose-cong reflexive (inr a b)) (symmetric (inr _ _))))

    case-cong : ∀ {X} {a c : Hom A X} {b d : Hom B X} → a ≈ c → b ≈ d → cases a b ≈ cases c d
    case-cong p q = case-ext _ _ (transitive (inl _ _) (transitive p (symmetric (inl _ _))))
                                 (transitive (inr _ _) (transitive q (symmetric (inr _ _))))

    exchange : ∀ (f : Hom A D) (g : Hom B D) (h : Hom A E) (k : Hom B E) →
               cases (pair f h) (pair g k) ≈ pair (cases f g) (cases h k)
    exchange f g h k = pair-ext _ _
      (transitive (project l _ _) (transitive (case-cong (left f h) (left g k)) (symmetric (left _ _))))
      (transitive (project r _ _) (transitive (case-cong (right f h) (right g k)) (symmetric (right _ _))))
