{-# OPTIONS --safe --without-K #-}
module AoP.ContextMinimumDistribution where

open import AoP.Prelude
open import AoP.Relations using (_←_; _⊆_; _∘_; _˘; _⊓_)
open import AoP.Thinning using (Min)

-- Exercise 7.35. The context of a child comparison is a common
-- source under S. A selected minimum and a feasible rival meet
-- precisely this extra constraint. Lift it before evaluating f.
module Law {A B : Set} (F : Set → Set) (L : ∀ {X Y} → Y ← X → F Y ← F X)
  (mono : ∀ {X Y} (P Q : Y ← X) → P ⊆ Q → L P ⊆ L Q)
  (join : ∀ {X Y Z} (P : Z ← Y) (Q : Y ← X) → L P ∘ L Q ⊆ L (P ∘ Q))
  (conv : ∀ {X Y} (P : Y ← X) → (L P) ˘ ⊆ L (P ˘))
  (S : B ← A) (R : B ← B) (f : F B → B) where
  M : B ← A
  M b a = Min R b (λ x → S x a)
  Guard = R ⊓ (S ∘ S ˘)
  compare-child : M ∘ S ˘ ⊆ Guard
  compare-child (a , (feasible , least) , rival) = least _ rival , a , feasible , rival
  Outcomes : B ← F A
  Outcomes b t = Σ (F B) λ v → (f v ≡ b) × L S v t
  distribute : (∀ {u v} → L Guard u v → R (f u) (f v)) → ∀ {u t} → L M u t → Min R (f u) (λ b → Outcomes b t)
  distribute ordered {u} {t} picked = (u , refl , mono M S fst picked) , lower
    where lower : ∀ b → Outcomes b t → R (f u) b
          lower _ (v , refl , rival) = ordered (mono (M ∘ S ˘) Guard compare-child
            (join M (S ˘) (t , picked , conv S rival)))
