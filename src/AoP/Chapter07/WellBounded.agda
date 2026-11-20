{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.WellBounded where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter08.Thinning using (Min)
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)

-- Exercises 7.26–7.28. Well-boundedness supplies a minimum when
-- given an actual member; it makes no demand on the empty set.
Bounded : ∀ {A} → (A ← A) → Set₁
Bounded {A} R = ∀ (X : A → Set) a → X a → Σ A λ b → Min R b X

connected : ∀ {A} {R : A ← A} → Bounded R → ∀ a b → R a b ⊎ R b a
connected wb a b with wb (λ c → (c ≡ a) ⊎ (c ≡ b)) a (inl refl)
... | _ , inl refl , lower = inl (lower b (inr refl))
... | _ , inr refl , lower = inr (lower a (inl refl))

-- Compare in the codomain on the image of X. Membership of the
-- returned minimum carries its preimage in X, even if f has collisions.
pull : ∀ {A B} (f : A → B) {R : B ← B} → Bounded R → Bounded (λ x y → R (f x) (f y))
pull {A} f wb X a xa with wb (λ b → Σ A λ c → X c × (f c ≡ b)) (f a) (a , xa , refl)
... | _ , (c , xc , refl) , lower = c , xc , λ d xd → lower (f d) (d , xd , refl)

module Cover {A : Set} (R : A ← A) where
  Covers = ∀ (X : A → Set) a → X a → Σ A λ b → R b a × Min R b X
  cover : Bounded R → Covers
  cover wb X a xa with wb X a xa
  ... | b , xb , lower = b , lower a xa , xb , lower
  bounded : Covers → Bounded R
  bounded cov X a xa with cov X a xa
  ... | b , edge , minimum = b , minimum
