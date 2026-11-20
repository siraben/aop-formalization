{-# OPTIONS --safe --without-K #-}
module AoP.Chapter02.MembershipImageUnion where

open import AoP.Common.Prelude
open import AoP.Chapter04.Power using (ℙ)
open import Agda.Primitive using (Level; _⊔_)

-- §2.2. The input elements of this relation are themselves subsets.
-- Keep the source and edge levels independent: ℙ A is in Set₁.
image : ∀ {i j r p : Level} {I : Set i} {J : Set j} →
        (J → I → Set r) → (I → Set p) → J → Set (i ⊔ r ⊔ p)
image {I = I} R X y = Σ I (λ x → Σ (R y x) (λ _ → X x))

module Family {A : Set} (chosen : ℙ A → Set) where
  belongs : A → ℙ A → Set
  belongs a S = S a
  -- An output a comes with the chosen subset supplying it. This is
  -- precisely the witness needed for union, even for an empty family.
  union = image belongs chosen
  include : ∀ S → chosen S → ∀ a → S a → union a
  include S select a member = S , (member , select)
  least : ∀ (T : ℙ A) → (∀ S → chosen S → ∀ a → S a → T a) → ∀ a → union a → T a
  least T contains a (S , (member , select)) = contains S select a member
