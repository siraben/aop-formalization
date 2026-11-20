{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.PolynomialSubstitution where

open import AoP.Common.Prelude
open import AoP.Chapter02.Polynomial

-- §2.5. To compose two unary polynomial expressions, replace every
-- variable of the outer expression by the inner expression. Constants
-- contain no variable to replace; products and sums retain their shape.
sub : Poly → Poly → Poly
sub I G = G
sub (K A) G = K A
sub (F ⊗ H) G = sub F G ⊗ sub H G
sub (F ⊕ H) G = sub F G ⊕ sub H G

-- Read a value of the resulting expression as a nested value. The
-- inverse descends the same outer shape. Neither operation changes a
-- tag, a constant, or the order of the two factors.
nest : ∀ F G {X} → ⟦ sub F G ⟧ X → ⟦ F ⟧ (⟦ G ⟧ X)
nest I G x = x
nest (K _) G x = x
nest (F ⊗ H) G (x , y) = nest F G x , nest H G y
nest (F ⊕ H) G (inl x) = inl (nest F G x)
nest (F ⊕ H) G (inr y) = inr (nest H G y)
flat : ∀ F G {X} → ⟦ F ⟧ (⟦ G ⟧ X) → ⟦ sub F G ⟧ X
flat I G x = x
flat (K _) G x = x
flat (F ⊗ H) G (x , y) = flat F G x , flat H G y
flat (F ⊕ H) G (inl x) = inl (flat F G x)
flat (F ⊕ H) G (inr y) = inr (flat H G y)

recover : ∀ F G {X} (x : ⟦ sub F G ⟧ X) → flat F G (nest F G x) ≡ x
recover I G x = refl
recover (K _) G x = refl
recover (F ⊗ H) G (x , y) rewrite recover F G x | recover H G y = refl
recover (F ⊕ H) G (inl x) = cong inl (recover F G x)
recover (F ⊕ H) G (inr y) = cong inr (recover H G y)
restore : ∀ F G {X} (x : ⟦ F ⟧ (⟦ G ⟧ X)) → nest F G (flat F G x) ≡ x
restore I G x = refl
restore (K _) G x = refl
restore (F ⊗ H) G (x , y) rewrite restore F G x | restore H G y = refl
restore (F ⊕ H) G (inl x) = cong inl (restore F G x)
restore (F ⊕ H) G (inr y) = cong inr (restore H G y)

-- Arrow action: mapping the substituted expression amounts to mapping
-- the inner expression at each variable position of the outer one.
natural : ∀ F G {X Y} (f : X → Y) (x : ⟦ sub F G ⟧ X) →
  nest F G (map (sub F G) f x) ≡ map F (map G f) (nest F G x)
natural I G f x = refl
natural (K _) G f x = refl
natural (F ⊗ H) G f (x , y) rewrite natural F G f x | natural H G f y = refl
natural (F ⊕ H) G f (inl x) = cong inl (natural F G f x)
natural (F ⊕ H) G f (inr y) = cong inr (natural H G f y)

-- The running example A + X × A has just one variable position.
Layer : Set → Poly
Layer A = K A ⊕ (I ⊗ K A)
branch : ∀ {A X Y} (f : X → Y) x (a : A) → map (Layer A) f (inr (x , a)) ≡ inr (f x , a)
branch f x a = refl
constant : ∀ {A X Y} (f : X → Y) (a : A) → map (Layer A) f (inl a) ≡ inl a
constant f a = refl
