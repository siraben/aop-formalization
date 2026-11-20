{-# OPTIONS --safe --without-K #-}
module AoP.ThinUnion where

open import AoP.Prelude
open import AoP.Relations using (_←_)
open import AoP.Thinning using (Pred; Thin; thin)
open import AoP.Power using (_≐_)
open import AoP.Polynomial using (_⊎_; inl; inr)

-- Exercise 8.4. Start with one valid thinning and put back any
-- subset of the original candidates. Inclusion still holds and the
-- old witnesses still cover the input. The second set needs no
-- dominance witnesses of its own.
module Law {A : Set} {R Q : A ← A} {X Y Z : Pred A} where
  Union : Pred A
  Union a = X a ⊎ Y a

  restore : Thin R X Z → (∀ a → Y a → Z a) → Thin R Union Z
  restore p sub = thin (λ { (inl x) → Thin.subset p x ; (inr y) → sub _ y }) cover
    where cover : ∀ b → Z b → Σ A λ a → Union a × R a b
          cover b z with Thin.cover p b z
          ... | a , x , ab = a , inl x , ab

  two : Thin R X Z → Thin Q Y Z → Thin R Union Z
  two p q = restore p (λ _ → Thin.subset q)

  members : ∀ a b → X a × Y b → Union a × Union b
  members a b (x , y) = inl x , inr y

-- For equal comparison relations the reverse inclusion takes the
-- very same thinning twice. Compare predicate unions extensionally.
duplicate : ∀ {A} {R : A ← A} {X Z : Pred A} → Thin R X Z →
            Σ (Pred A) λ U → Σ (Pred A) λ V → Thin R U Z × (Thin R V Z × (X ≐ (λ a → U a ⊎ V a)))
duplicate {X = X} p = X , X , p , p , (λ _ x → inl x) , (λ { _ (inl x) → x ; _ (inr x) → x })
