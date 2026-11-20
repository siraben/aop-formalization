{-# OPTIONS --safe --without-K #-}
module AoP.Chapter08.BranchNetwork where

open import AoP.Common.Prelude
open import AoP.Chapter08.Thinning using (Thin; thin)
open import AoP.Common.NatOrder using (_≤_; rid; sum-mono)
open import Agda.Builtin.Nat using (Nat; _+_)

-- Exercise 8.10. Each fork routes from a parent to two prescribed
-- child starts. Their routes are independent once this fork is fixed.
-- J = A labels internal nodes; a singleton J gives unlabelled forks.
module Network {A J V : Set} (Stop : A → V → Set)
  (Fork : J → V → V → V → Set)
  (weight : ∀ {j u v w} → Fork j u v w → Nat) where
  data Shape : Set where
    tip : A → Shape
    node : J → Shape → Shape → Shape
  data Route : Shape → V → Set where
    end : ∀ {a u} → Stop a u → Route (tip a) u
    fork : ∀ {j u v w l r} → Fork j u v w → Route l v → Route r w → Route (node j l r) u
  cost : ∀ {s u} → Route s u → Nat
  cost (end _) = 0
  cost (fork e x y) = weight e + (cost x + cost y)
  Layer : Shape → Set₁
  Layer s = ∀ u → Route s u → Set
  Covers : ∀ {s} → Layer s → Layer s → Set
  Covers X Y = ∀ u → Thin (λ p q → cost p ≤ cost q) (X u) (Y u)
  combine : ∀ j {l r} → Layer l → Layer r → Layer (node j l r)
  combine j X Y _ (fork _ x y) = X _ x × Y _ y
  lift : ∀ j {l r} {L L′ : Layer l} {R R′ : Layer r} → Covers L L′ → Covers R R′ → Covers (combine j L R) (combine j L′ R′)
  Thin.subset (lift j left right u) {fork e x y} (lx , ry) = Thin.subset (left _) lx , Thin.subset (right _) ry
  Thin.cover (lift j left right u) (fork e x y) (lx , ry) with Thin.cover (left _) x lx | Thin.cover (right _) y ry
  ... | x′ , hx , le | y′ , hy , ge = fork e x′ y′ , (hx , hy) , sum-mono (rid (weight e)) (sum-mono le ge)
  -- A bottom-up table may thin again after combining the two layers.
  module Table (rows : ∀ s → Layer s)
    (base : ∀ a → Covers (rows (tip a)) (λ _ _ → 0 ≡ 0))
    (prune : ∀ j l r → Covers (rows (node j l r)) (combine j (rows l) (rows r))) where
    correct : ∀ s → Covers (rows s) (λ _ _ → 0 ≡ 0)
    correct (tip a) = base a
    Thin.subset (correct (node j l r) u) _ = refl
    Thin.cover (correct (node j l r) u) (fork e x y) _ with Thin.cover (correct l _) x refl | Thin.cover (correct r _) y refl
    ... | x′ , hx , le | y′ , hy , ge with Thin.cover (prune j l r u) (fork e x′ y′) (hx , hy)
    ... | p , member , bound = p , member , AoP.Common.NatOrder.chain bound (sum-mono (rid (weight e)) (sum-mono le ge))
