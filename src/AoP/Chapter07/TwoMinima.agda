{-# OPTIONS --safe --without-K #-}
module AoP.Chapter07.TwoMinima where

open import AoP.Common.Prelude
open import AoP.Chapter04.Relations
open import AoP.Chapter02.Polynomial using (_⊎_; inl; inr)
open import AoP.Chapter08.Thinning using (Min)

-- Exercise 7.8. When a precedes b under R and b precedes a under S,
-- the two-element set {a,b} witnesses a common input to min R and
-- min S. Conversely any common input contains both elements, so the
-- lower-bound fields supply the two comparison edges directly.
module Law {A : Set} (R S : A ← A) where
  Shared : A → A → Set₁
  Shared a b = Σ (A → Set) λ X → Min R a X × Min S b X

  edges : ∀ {a b} → Shared a b → R a b × S b a
  edges (X , (a∈ , lowerR) , b∈ , lowerS) = lowerR _ b∈ , lowerS _ a∈

  witness : (∀ a → R a a) → (∀ b → S b b) → ∀ {a b} → R a b × S b a → Shared a b
  witness rr ss {a} {b} (ab , ba) = (λ x → (x ≡ a) ⊎ (x ≡ b)) ,
    (inl refl , (λ { _ (inl refl) → rr a ; _ (inr refl) → ab })) ,
    inr refl , (λ { _ (inl refl) → ba ; _ (inr refl) → ss b })
